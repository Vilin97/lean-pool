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
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.Finset.Max

/-! # Uniform Smallness -/

@[expose] public noncomputable section

open Metric Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-- Joint continuity on `ℝ × closedBall x₀ ρ` gives uniform smallness of
`F t y - F t₀ y` over `y ∈ closedBall x₀ ρ` as `t → t₀`.

This is the Lebesgue-number argument: joint continuity at each `(t₀, y)` gives a
radius `r y`; finitely many spatial balls `ball y (r y / 2)` cover the compact
`closedBall x₀ ρ`; the minimum of the half-radii is the uniform `η`.

Note: the `[ProperSpace E]` hypothesis (e.g. from `FiniteDimensional.proper`
when `E` is finite-dimensional) is essential — `closedBall x₀ ρ` must be
compact. Without it the claim is false: on `E = ℓ²`, with `H : E → ℝ`
continuous and `H eₙ = n`, the map
`(t, y) ↦ max (0, 1 - |t| * H y) • e₀` is jointly continuous on
`ℝ × closedBall 0 1`, equals `e₀` at `t = 0`, yet
`sup_y ‖F t y - F 0 y‖ = 1` for every `t ≠ 0`. -/
theorem uniform_smallness_of_joint_continuous
    {F : ℝ → E → F'} {x₀ : E} {ρ : ℝ}
    (hjoint : ContinuousOn (fun p : ℝ × E => F p.1 p.2) (univ ×ˢ closedBall x₀ ρ))
    {t₀ : ℝ} :
    ∀ ε > 0, ∃ η > 0, ∀ t : ℝ, dist t t₀ < η →
      ∀ y ∈ closedBall x₀ ρ, ‖F t y - F t₀ y‖ < ε := by
  classical
  intro ε hε
  -- Trivial case: a negative radius gives an empty ball.
  by_cases hρ : ρ < 0
  · have hempty : closedBall x₀ ρ = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro y hy
      rw [mem_closedBall] at hy
      have hnn : (0 : ℝ) ≤ dist y x₀ := dist_nonneg
      linarith
    exact ⟨1, one_pos, fun t _ y hy => absurd (hempty ▸ hy) (notMem_empty y)⟩
  -- Main case: `0 ≤ ρ`, so the closed ball is nonempty and compact.
  push Not at hρ
  -- Step 1: radii from joint continuity at each `(t₀, y)`.
  -- (For `y` outside the ball we record the junk radius `1`; only positivity
  -- of `r` is used there.)
  have hr : ∀ y : E, ∃ r > 0, (y ∈ closedBall x₀ ρ →
      ∀ p ∈ ball (t₀, y) r ∩ (univ ×ˢ closedBall x₀ ρ),
        dist ((fun p : ℝ × E => F p.1 p.2) p)
          ((fun p : ℝ × E => F p.1 p.2) (t₀, y)) < ε / 2) := by
    intro y
    by_cases hy : y ∈ closedBall x₀ ρ
    · have hmem : (t₀, y) ∈ univ ×ˢ closedBall x₀ ρ := ⟨mem_univ _, hy⟩
      have hc := (continuousWithinAt_iff.mp (hjoint _ hmem)) (ε / 2) (half_pos hε)
      obtain ⟨δ, hδ, hδspec⟩ := hc
      exact ⟨δ, hδ, fun _ p hp => hδspec hp.2 (mem_ball.mp hp.1)⟩
    · exact ⟨1, one_pos, fun h => absurd h hy⟩
  choose r hr_pos hr_spec using hr
  -- Step 2: finite subcover of the compact ball by spatial half-radius balls.
  obtain ⟨T, hT⟩ := (isCompact_closedBall x₀ ρ).elim_finite_subcover
    (fun y : ↥(closedBall x₀ ρ) => ball (y : E) (r (y : E) / 2))
    (fun _ => isOpen_ball)
    (fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (half_pos (hr_pos z))⟩)
  -- Step 3: `T` is nonempty since `x₀` lies in the ball.
  have hx₀ : x₀ ∈ closedBall x₀ ρ := by
    rw [mem_closedBall, dist_self]; exact hρ
  obtain ⟨i₀, hi₀T', -⟩ := mem_iUnion₂.mp (hT hx₀)
  have hTne : T.Nonempty := ⟨i₀, Finset.mem_coe.mp hi₀T'⟩
  -- Step 4: the uniform radius is the minimum of the half-radii.
  have hpos : (0 : ℝ) <
      (T.image fun y : ↥(closedBall x₀ ρ) => r (y : E) / 2).min'
        (hTne.image fun y : ↥(closedBall x₀ ρ) => r (y : E) / 2) := by
    have hmem := Finset.min'_mem _
      (hTne.image fun y : ↥(closedBall x₀ ρ) => r (y : E) / 2)
    rw [Finset.mem_image] at hmem
    obtain ⟨y, -, hy⟩ := hmem
    rw [← hy]
    exact half_pos (hr_pos _)
  have hηle : ∀ z ∈ T,
      (T.image fun y : ↥(closedBall x₀ ρ) => r (y : E) / 2).min'
          (hTne.image fun y : ↥(closedBall x₀ ρ) => r (y : E) / 2)
        ≤ r (z : E) / 2 :=
    fun z hz => Finset.min'_le _ _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
  refine ⟨_, hpos, ?_⟩
  intro t ht y hy
  obtain ⟨i, hiT', hiy⟩ := mem_iUnion₂.mp (hT hy)
  have hiT : i ∈ T := Finset.mem_coe.mp hiT'
  have h2pos : (0 : ℝ) < r (i : E) := hr_pos _
  have h2half : r (i : E) / 2 < r (i : E) := half_lt_self h2pos
  have hmem_ball : dist y (i : E) < r (i : E) / 2 := mem_ball.mp hiy
  have htt : dist t t₀ < r (i : E) / 2 := lt_of_lt_of_le ht (hηle i hiT)
  -- `(t, y)` lies in the joint ball around `(t₀, i)`.
  have hdist : dist ((t, y) : ℝ × E) (t₀, (i : E)) < r (i : E) := by
    rw [Prod.dist_eq]
    show max (dist t t₀) (dist y (i : E)) < r (i : E)
    exact max_lt (lt_trans htt h2half) (lt_trans hmem_ball h2half)
  have hmem1 : ((t, y) : ℝ × E)
      ∈ ball (t₀, (i : E)) (r (i : E)) ∩ (univ ×ˢ closedBall x₀ ρ) :=
    ⟨mem_ball.mpr hdist, mem_univ _, hy⟩
  have e1 : dist (F t y) (F t₀ (i : E)) < ε / 2 := hr_spec _ i.2 _ hmem1
  -- `(t₀, y)` lies in the joint ball around `(t₀, i)` too.
  have hdist0 : dist ((t₀, y) : ℝ × E) (t₀, (i : E)) < r (i : E) := by
    rw [Prod.dist_eq]
    show max (dist t₀ t₀) (dist y (i : E)) < r (i : E)
    exact max_lt (by rw [dist_self]; exact h2pos) (lt_trans hmem_ball h2half)
  have hmem0 : ((t₀, y) : ℝ × E)
      ∈ ball (t₀, (i : E)) (r (i : E)) ∩ (univ ×ˢ closedBall x₀ ρ) :=
    ⟨mem_ball.mpr hdist0, mem_univ _, hy⟩
  have e0 : dist (F t₀ y) (F t₀ (i : E)) < ε / 2 := hr_spec _ i.2 _ hmem0
  -- Triangle inequality through `F t₀ i`.
  rw [dist_eq_norm] at e1 e0
  rw [norm_sub_rev] at e0
  calc ‖F t y - F t₀ y‖
      = ‖(F t y - F t₀ (i : E)) + (F t₀ (i : E) - F t₀ y)‖ := by congr 1; abel
    _ ≤ ‖F t y - F t₀ (i : E)‖ + ‖F t₀ (i : E) - F t₀ y‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add e1 e0
    _ = ε := by ring
