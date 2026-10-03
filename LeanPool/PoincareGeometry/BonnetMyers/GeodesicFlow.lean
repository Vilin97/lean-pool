/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.BonnetMyers.Geodesic

/-!
# Uniform local flows for the coordinate geodesic equation

The coordinate acceleration in `Geodesic` is only a local expression, but its
`C¹` regularity is enough to obtain a common existence interval for all nearby
initial position--velocity pairs.  This file records that analytic fact using
the pinned Picard--Lindelöf API.  No geodesic completeness or global flow is
assumed here.
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal Topology

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

namespace LocalGeodesicFlow

private lemma ball_prod_ball_subset_closedBall_Icc
    {V : Type*} [NormedAddCommGroup V] {q₀ : V} {r δ ε : ℝ}
    (hδε : δ ≤ ε) :
    Metric.ball q₀ r ×ˢ Metric.ball (0 : ℝ) δ ⊆
      Metric.closedBall q₀ r ×ˢ Icc (-ε) ε := by
  intro z hz
  refine ⟨Metric.mem_closedBall'.mpr (le_of_lt (Metric.mem_ball'.mp hz.1)), ?_⟩
  have hz' : |z.2| < δ := by
    simpa [Real.dist_eq] using (Metric.mem_ball'.mp hz.2)
  rw [abs_lt] at hz'
  constructor <;> linarith

/-- A `C¹` autonomous ODE has a continuous local flow on a common interval
for all initial states in a neighborhood of the chosen state.  The flow is
only asserted on that neighborhood and interval; its values elsewhere are
the harmless default values supplied by the Picard construction. -/
theorem exists_uniform_local_flow
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {F : V → V} {q₀ : V}
    (hF : ContDiffAt ℝ 1 F q₀) :
    ∃ U ∈ 𝓝 q₀, ∃ δ : ℝ, 0 < δ ∧
      ∃ α : V × ℝ → V,
        ContinuousOn α (U ×ˢ Metric.ball 0 δ) ∧
        ∀ q ∈ U, α (q, 0) = q ∧
          ∀ t ∈ Metric.ball 0 δ,
            HasDerivAt (fun s ↦ α (q, s)) (F (α (q, t))) t := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ :=
    IsPicardLindelof.of_contDiffAt_one hF
  let t₀ : Icc (-ε) ε := ⟨0, by constructor <;> linarith⟩
  obtain ⟨α₀, hα₀⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  let U : Set V := Metric.ball q₀ (r : ℝ)
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hU : U ∈ 𝓝 q₀ := by
    exact Metric.ball_mem_nhds q₀ (by exact_mod_cast hr)
  have hsub : U ×ˢ Metric.ball (0 : ℝ) δ ⊆
      Metric.closedBall q₀ (r : ℝ) ×ˢ Icc (0 - ε) (0 + ε) := by
    have hsub' := ball_prod_ball_subset_closedBall_Icc
      (q₀ := q₀) (r := (r : ℝ)) (δ := δ) (ε := ε)
      (by dsimp [δ]; linarith)
    simpa only [U, zero_sub, zero_add] using hsub'
  refine ⟨U, hU, δ, hδ, α₀, hα₀.2.mono hsub, ?_⟩
  intro q hq
  have hq' : q ∈ Metric.closedBall q₀ (r : ℝ) :=
    Metric.mem_closedBall'.mpr (le_of_lt (Metric.mem_ball'.mp hq))
  constructor
  · simpa using (hα₀.1 q hq').1
  · intro t ht
    have ht' : t ∈ Icc (0 - ε) (0 + ε) :=
      by
        have hq_ball : q ∈ Metric.ball q₀ (r : ℝ) := by
          simpa only [U] using hq
        have hpair : (q, t) ∈
            Metric.ball q₀ (r : ℝ) ×ˢ Metric.ball (0 : ℝ) δ :=
          ⟨hq_ball, ht⟩
        have ht₀ : t ∈ Icc (-ε) ε :=
          (ball_prod_ball_subset_closedBall_Icc (q₀ := q₀)
            (r := (r : ℝ)) (δ := δ) (ε := ε)
            (by dsimp [δ]; linarith)) hpair |>.2
        simpa only [zero_sub, zero_add] using ht₀
    have hderiv := (hα₀.1 q hq').2 t ht'
    have ht_abs : |t| < δ := by
      simpa [Real.dist_eq] using (Metric.mem_ball'.mp ht)
    have ht_lower : 0 - ε < t := by
      rcases (abs_lt.mp ht_abs) with ⟨ht_lower, ht_upper⟩
      dsimp [δ] at ht_lower ht_upper
      linarith
    have ht_upper : t < 0 + ε := by
      rcases (abs_lt.mp ht_abs) with ⟨ht_lower, ht_upper⟩
      dsimp [δ] at ht_lower ht_upper
      linarith
    exact hderiv.hasDerivAt (Icc_mem_nhds ht_lower ht_upper)

end LocalGeodesicFlow

namespace LocalGeodesicData

variable [RiemannianBundle (TangentSpace I : M → Type _)]

/-- The actual coordinate geodesic system has a common continuous local flow
near every initial pair in the chart. -/
theorem exists_uniform_coordinateGeodesic_flow
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {z u : E} (hz : z ∈ (extChartAt I x₀).target) :
    ∃ U ∈ 𝓝 (z, u), ∃ δ : ℝ, 0 < δ ∧
      ∃ α : (E × E) × ℝ → E × E,
        ContinuousOn α (U ×ˢ Metric.ball 0 δ) ∧
        ∀ q ∈ U, α (q, 0) = q ∧
          ∀ t ∈ Metric.ball 0 δ,
            HasDerivAt (fun s ↦ α (q, s))
              (secondOrderSystem
                (coordinateAcceleration (I := I) (M := M) (E := E) cov x₀ b)
                (α (q, t))) t := by
  have hF := coordinateAcceleration_system_contDiffAt_of_mem_target
    (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b) hz u
  obtain ⟨U, hU, δ, hδ, α, hαc, hα⟩ :=
    LocalGeodesicFlow.exists_uniform_local_flow
      (F := secondOrderSystem
        (coordinateAcceleration (I := I) (M := M) (E := E) cov x₀ b)) hF
  exact ⟨U, hU, δ, hδ, α, hαc, hα⟩

end LocalGeodesicData

end BonnetMyersEntry
