/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Path.LocalPrimitive
import Mathlib.Topology.UnitInterval

/-!
# `ChartChain`: a Lebesgue-number chart subdivision along a path (CC6)

Unit: paths-and-integrals (`docs/design/paths-and-integrals.md` §3.1). A subdivision of `[0,1]`
with chart-and-ball data adapted to a path `γ`, obtained from mathlib's 1D Lebesgue-number lemma
`exists_monotone_Icc_subset_open_cover_unitInterval` applied to the cover of `I` by preimages of
chart-balls along `γ`.

Main declarations:
* `RS.ChartChain γ` — the subdivision structure.
* `RS.exists_chartChain` — existence, for any continuous path `γ`.
-/

open scoped ContDiff Manifold Topology unitInterval
open IsManifold Metric Set Filter

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {x y : X}

/-- A subdivision of `[0,1]` with chart-and-ball data adapted to `γ`: on each piece
`Icc (t k) (t (k+1))`, `γ` stays inside a single chart `e k` with image inside a ball
`ball (c k) (r k) ⊆ (e k).target`. -/
structure ChartChain (γ : Path x y) where
  /-- The number of steps in the chain. -/
  n : ℕ
  /-- The subdivision times. -/
  t : ℕ → ℝ
  ht0 : t 0 = 0
  ht1 : ∀ k, n ≤ k → t k = 1
  mono : Monotone t
  /-- The chart used on each step. -/
  e : ℕ → OpenPartialHomeomorph X ℂ
  he : ∀ k, e k ∈ maximalAtlas 𝓘(ℂ) ω X
  /-- The centre of each step's disc, in that step's chart. -/
  c : ℕ → ℂ
  /-- The radius of each step's disc. -/
  r : ℕ → ℝ
  hr : ∀ k, 0 < r k
  ball_subset : ∀ k, ball (c k) (r k) ⊆ (e k).target
  maps : ∀ k, ∀ u ∈ Icc (t k) (t (k + 1)),
    γ.extend u ∈ (e k).source ∧ e k (γ.extend u) ∈ ball (c k) (r k)

/-- For every `τ ∈ I`, an open (in `I`) neighbourhood `V` of `τ` and chart-ball data
`(e, c, r)` such that `γ.extend` maps `V` into `e.source` with image inside
`ball c r ⊆ e.target`. -/
private theorem exists_chart_nhds (γ : Path x y) (τ : ↥unitInterval) :
    ∃ V : Set ↥unitInterval, IsOpen V ∧ τ ∈ V ∧
      ∃ (e : OpenPartialHomeomorph X ℂ) (c : ℂ) (r : ℝ), e ∈ maximalAtlas 𝓘(ℂ) ω X ∧ 0 < r ∧
        ball c r ⊆ e.target ∧ ∀ u ∈ V, γ.extend (u : ℝ) ∈ e.source ∧
          e (γ.extend (u : ℝ)) ∈ ball c r := by
  set eτ : OpenPartialHomeomorph X ℂ := chartAt ℂ (γ.extend (τ : ℝ)) with heτ_def
  obtain ⟨rτ, hrτ, hballτ⟩ := Metric.isOpen_iff.mp eτ.open_target (eτ (γ.extend (τ : ℝ)))
    (mem_chart_target ℂ (γ.extend (τ : ℝ)))
  set U : Set X := eτ.source ∩ eτ ⁻¹' (ball (eτ (γ.extend (τ : ℝ))) rτ) with hU_def
  have hUopen : IsOpen U := eτ.isOpen_inter_preimage isOpen_ball
  set V : Set ↥unitInterval := (fun u : ↥unitInterval => γ.extend (u : ℝ)) ⁻¹' U with hV_def
  have hVopen : IsOpen V :=
    (γ.continuous_extend.comp continuous_subtype_val).isOpen_preimage U hUopen
  have hτV : τ ∈ V := ⟨mem_chart_source ℂ (γ.extend (τ : ℝ)), mem_ball_self hrτ⟩
  exact ⟨V, hVopen, hτV, eτ, eτ (γ.extend (τ : ℝ)), rτ, chart_mem_maximalAtlas _, hrτ, hballτ,
    fun u hu => hu⟩

theorem exists_chartChain (γ : Path x y) : Nonempty (ChartChain γ) := by
  choose V hVopen hτV e c r he hr hballsub hmaps using exists_chart_nhds γ
  obtain ⟨t, ht0, hmono, ⟨n, htn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hVopen (fun τ _ => mem_iUnion.2 ⟨τ, hτV τ⟩)
  choose iOf hiOf using hsub
  refine ⟨⟨n, fun k => (t k : ℝ), by simp [ht0], ?_, ?_, fun k => e (iOf k), fun k => he (iOf k),
    fun k => c (iOf k), fun k => r (iOf k), fun k => hr (iOf k), fun k => hballsub (iOf k), ?_⟩⟩
  · intro k hk
    simp [htn k hk]
  · intro a b hab
    exact hmono hab
  · intro k u hu
    have hu' : (t k : ℝ) ≤ u ∧ u ≤ (t (k + 1) : ℝ) := hu
    have hu01 : u ∈ (unitInterval : Set ℝ) :=
      ⟨(t k).2.1.trans hu'.1, hu'.2.trans (t (k + 1)).2.2⟩
    have hmem : (⟨u, hu01⟩ : ↥unitInterval) ∈ Icc (t k) (t (k + 1)) := hu'
    exact hmaps (iOf k) _ (hiOf k hmem)

end RS

end
