/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.NormedDirectLimit

/-!
# Coherent retractions on a completed normed direct limit

This file formalizes the linear part of the recovery mechanism at a limit
stage. A coherent family of contractive projections to an earlier component
extends to a contractive linear map from the completed direct limit.
-/

namespace ScottishBook155

universe u

namespace CoherentRetractionLimit

open Filter

variable {ι : Type u} [LinearOrder ι] [Nonempty ι]
variable (N : ι → Type u)
variable [∀ i, NormedAddCommGroup (N i)] [∀ i, NormedSpace ℝ (N i)]
variable [∀ i, CompleteSpace (N i)]
variable (e : ∀ i j : ι, i ≤ j → N i →ₗᵢ[ℝ] N j)
variable [DirectedSystem N (e · · ·)]

noncomputable local instance : DecidableEq ι := Classical.decEq ι

local instance linearDirectedSystem :
    DirectedSystem N (NormedDirectLimit.linearMap N e · · ·) where
  map_self {i} x := DirectedSystem.map_self (f := (e · · ·)) x
  map_map {k j i} hij hjk x :=
    DirectedSystem.map_map (f := (e · · ·)) hij hjk x

/-- A projection to a fixed earlier component, defined coherently on every
component of the directed system. -/
structure ProjectionFamily (a : ι) where
  project : ∀ i, N i →L[ℝ] N a
  coherent : ∀ i j (hij : i ≤ j) x,
    project j (e i j hij x) = project i x
  contractive : ∀ i x, ‖project i x‖ ≤ ‖x‖
  leftInverse : ∀ x, project a x = x

/-- The projection family induces a contractive linear map from the completed
direct limit. -/
noncomputable def ProjectionFamily.completedProjection {a : ι}
    (P : ProjectionFamily N e a) :
    NormedDirectLimit.CompletedCarrier N e →L[ℝ] N a :=
  NormedDirectLimit.completedLift N e P.project P.coherent 1 (by
    intro i x
    simpa using P.contractive i x)

@[simp]
theorem ProjectionFamily.completedProjection_completedOf {a : ι}
    (P : ProjectionFamily N e a) (i : ι) (x : N i) :
    ProjectionFamily.completedProjection N e P
        (NormedDirectLimit.completedOf N e i x) = P.project i x := by
  exact NormedDirectLimit.completedLift_completedOf N e P.project P.coherent 1
    (by
      intro j y
      simpa using P.contractive j y) i x

/-- The completed projection retracts the canonical copy of its chosen
component. -/
theorem ProjectionFamily.completedProjection_retracts {a : ι}
    (P : ProjectionFamily N e a) (x : N a) :
    ProjectionFamily.completedProjection N e P
        (NormedDirectLimit.completedOf N e a x) = x := by
  rw [ProjectionFamily.completedProjection_completedOf N e P]
  exact P.leftInverse x

/-- The completed projection is contractive. -/
theorem ProjectionFamily.completedProjection_norm_le {a : ι}
    (P : ProjectionFamily N e a)
    (z : NormedDirectLimit.CompletedCarrier N e) :
    ‖ProjectionFamily.completedProjection N e P z‖ ≤ ‖z‖ := by
  exact NormedDirectLimit.completedLift_norm_le_one N e P.project P.coherent
    P.contractive z

/-- Coherent projections to every component of the directed system. Below
the projection index they are the forward embeddings; above it they are the
specified retractions. -/
structure ProjectionSystem where
  project : ∀ a i, N i →L[ℝ] N a
  coherent : ∀ a i j (hij : i ≤ j) x,
    project a j (e i j hij x) = project a i x
  contractive : ∀ a i x, ‖project a i x‖ ≤ ‖x‖
  identityBelow : ∀ i a (hia : i ≤ a) x,
    project a i x = e i a hia x

/-- The projection system restricted to one fixed component. -/
noncomputable def ProjectionSystem.family (P : ProjectionSystem N e) (a : ι) :
    ProjectionFamily N e a where
  project := P.project a
  coherent := P.coherent a
  contractive := P.contractive a
  leftInverse x := by
    rw [P.identityBelow a a le_rfl]
    exact DirectedSystem.map_self (f := (e · · ·)) x

/-- Project a completed-limit vector to component `a` and include it back
into the completed limit. -/
noncomputable def ProjectionSystem.approx (P : ProjectionSystem N e) (a : ι)
    (z : NormedDirectLimit.CompletedCarrier N e) :
    NormedDirectLimit.CompletedCarrier N e :=
  NormedDirectLimit.completedOf N e a
    (ProjectionFamily.completedProjection N e
      (ProjectionSystem.family N e P a) z)

/-- Once `a` lies above a component, approximation fixes that entire
component pointwise. -/
theorem ProjectionSystem.approx_completedOf_of_le
    (P : ProjectionSystem N e) {i a : ι} (hia : i ≤ a) (x : N i) :
    ProjectionSystem.approx N e P a
        (NormedDirectLimit.completedOf N e i x) =
      NormedDirectLimit.completedOf N e i x := by
  rw [ProjectionSystem.approx,
    ProjectionFamily.completedProjection_completedOf N e
      (ProjectionSystem.family N e P a),
    ProjectionSystem.family, P.identityBelow i a hia,
    NormedDirectLimit.completedOf_f]

/-- Every approximation map is nonexpansive. -/
theorem ProjectionSystem.approx_dist_le
    (P : ProjectionSystem N e) (a : ι)
    (z w : NormedDirectLimit.CompletedCarrier N e) :
    dist (ProjectionSystem.approx N e P a z)
        (ProjectionSystem.approx N e P a w) ≤ dist z w := by
  rw [ProjectionSystem.approx, ProjectionSystem.approx,
    (NormedDirectLimit.completedOf N e a).isometry.dist_eq,
    dist_eq_norm, ← map_sub, dist_eq_norm]
  exact ProjectionFamily.completedProjection_norm_le N e
    (ProjectionSystem.family N e P a) (z - w)

/-- Coherent contractive projections converge strongly to the identity on
the completed direct limit. -/
theorem ProjectionSystem.approx_tendsto
    (P : ProjectionSystem N e)
    (z : NormedDirectLimit.CompletedCarrier N e) :
    Tendsto (fun a => ProjectionSystem.approx N e P a z) atTop (nhds z) := by
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨c, ⟨d, rfl⟩, hcz⟩ :=
    SeminormedAddCommGroup.mem_closure_iff.mp
      (UniformSpace.Completion.isDenseInducing_coe.dense z) (ε / 2) hhalf
  obtain ⟨i, x, hxi⟩ := Module.DirectLimit.exists_of d
  refine ⟨i, fun a hia => ?_⟩
  have hdist : dist (↑d : NormedDirectLimit.CompletedCarrier N e) z < ε / 2 := by
    simpa [dist_eq_norm, norm_sub_rev] using hcz
  have hfix : ProjectionSystem.approx N e P a (↑d) = (↑d) := by
    rw [← hxi]
    exact ProjectionSystem.approx_completedOf_of_le N e P hia x
  calc
    dist (ProjectionSystem.approx N e P a z) z ≤
        dist (ProjectionSystem.approx N e P a z)
            (ProjectionSystem.approx N e P a (↑d)) +
          dist (ProjectionSystem.approx N e P a (↑d)) z := dist_triangle _ _ _
    _ = dist (ProjectionSystem.approx N e P a z)
        (ProjectionSystem.approx N e P a (↑d)) + dist (↑d) z := by
      rw [hfix]
    _ ≤ dist z (↑d) + dist (↑d) z :=
      add_le_add (ProjectionSystem.approx_dist_le N e P a z (↑d)) le_rfl
    _ < ε := by
      rw [dist_comm z]
      linarith [hdist]

/-- For a positive recovery band, every completed-limit vector eventually
lies within that band of its projected approximation. -/
theorem ProjectionSystem.eventually_dist_approx_le
    (P : ProjectionSystem N e) {L : ℝ} (hL : 0 < L)
    (z : NormedDirectLimit.CompletedCarrier N e) :
    ∀ᶠ a in atTop, dist z (ProjectionSystem.approx N e P a z) ≤ L := by
  have ht : Tendsto (fun a => dist z (ProjectionSystem.approx N e P a z))
      atTop (nhds 0) :=
    by simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ι => z) atTop (nhds z)).dist
        (ProjectionSystem.approx_tendsto N e P z))
  have hevent : ∀ᶠ a in atTop,
      dist z (ProjectionSystem.approx N e P a z) < L := by
    exact ((Metric.tendsto_nhds.mp ht) L hL).mono fun _ h => by
      simpa [Real.dist_eq, abs_of_nonneg dist_nonneg] using h
  exact hevent.mono fun _ h => h.le

/-- Strict form of eventual approximation, used when the recovery invariant
is stated on an open band. -/
theorem ProjectionSystem.eventually_dist_approx_lt
    (P : ProjectionSystem N e) {L : ℝ} (hL : 0 < L)
    (z : NormedDirectLimit.CompletedCarrier N e) :
    ∀ᶠ a in atTop, dist z (ProjectionSystem.approx N e P a z) < L := by
  have ht : Tendsto (fun a => dist z (ProjectionSystem.approx N e P a z))
      atTop (nhds 0) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ι => z) atTop (nhds z)).dist
        (ProjectionSystem.approx_tendsto N e P z))
  exact ((Metric.tendsto_nhds.mp ht) L hL).mono fun _ h => by
    simpa [Real.dist_eq, abs_of_nonneg dist_nonneg] using h

end CoherentRetractionLimit

end ScottishBook155
