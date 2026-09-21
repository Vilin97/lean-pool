/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.CoherentRetractionLimit

/-!
# Coherent bidirectional systems

An increasing family of normed spaces equipped with coherent contractive
retractions supplies both a directed system and the projection system used at
completed limit stages.
-/

namespace ScottishBook155

universe u

/-- Forward linear isometries together with coherent backward contractive
projections. -/
structure CoherentBiSystem {ι : Type u} [LinearOrder ι]
    (G : ι → Type u)
    [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)] where
  /-- Compatible linear isometric embeddings from earlier stages into later stages. -/
  embed : ∀ i j, i ≤ j → G i →ₗᵢ[ℝ] G j
  /-- Contractive continuous linear projections from later stages back to earlier stages. -/
  project : ∀ i j, i ≤ j → G j →L[ℝ] G i
  embed_refl : ∀ i x, embed i i le_rfl x = x
  embed_trans : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k) x,
    embed j k hjk (embed i j hij x) = embed i k (hij.trans hjk) x
  project_embed : ∀ a i j (hai : a ≤ i) (hij : i ≤ j) x,
    project a j (hai.trans hij) (embed i j hij x) = project a i hai x
  project_retracts : ∀ i j (hij : i ≤ j) x,
    project i j hij (embed i j hij x) = x
  project_contractive : ∀ i j (hij : i ≤ j) x,
    ‖project i j hij x‖ ≤ ‖x‖

namespace CoherentBiSystem

variable {ι : Type u} [LinearOrder ι]
variable (G : ι → Type u)
variable [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)]

/-- A coherent bidirectional system is determined by its forward and backward
maps; all coherence and norm fields are propositions. -/
theorem ext {B D : CoherentBiSystem G}
    (hembed : B.embed = D.embed) (hproject : B.project = D.project) : B = D := by
  cases B
  cases D
  dsimp at hembed hproject ⊢
  cases hembed
  cases hproject
  rfl

/-- A coherent bidirectional system gives Mathlib's directed-system
coherence for its forward embeddings. -/
noncomputable instance directedSystem (B : CoherentBiSystem G) :
    DirectedSystem G (B.embed · · ·) where
  map_self {i} x := B.embed_refl i x
  map_map {k j i} hij hjk x := B.embed_trans i j k hij hjk x

/-- Projection from any component to component `a`: embed forward below `a`,
and retract backward above `a`. -/
noncomputable def totalProject (B : CoherentBiSystem G) (a i : ι) :
    G i →L[ℝ] G a := by
  by_cases hia : i ≤ a
  · exact (B.embed i a hia).toContinuousLinearMap
  · exact B.project a i (le_of_lt (lt_of_not_ge hia))

theorem totalProject_of_le (B : CoherentBiSystem G)
    {i a : ι} (hia : i ≤ a) (x : G i) :
    totalProject G B a i x = B.embed i a hia x := by
  rw [totalProject]
  split_ifs
  rfl

theorem totalProject_of_ge (B : CoherentBiSystem G)
    {a i : ι} (hai : a ≤ i) (x : G i) :
    totalProject G B a i x = B.project a i hai x := by
  by_cases hia : i ≤ a
  · have hai' : a = i := le_antisymm hai hia
    subst i
    rw [totalProject_of_le G B le_rfl, B.embed_refl]
    have hp : B.project a a hai x = x := by
      simpa only [B.embed_refl] using B.project_retracts a a hai x
    exact hp.symm
  · rw [totalProject]
    split_ifs
    congr

/-- The total projections form the projection system required at a completed
direct limit. -/
noncomputable def projectionSystem (B : CoherentBiSystem G) :
    CoherentRetractionLimit.ProjectionSystem G B.embed where
  project := totalProject G B
  coherent a i j hij x := by
    by_cases hja : j ≤ a
    · have hia : i ≤ a := hij.trans hja
      rw [totalProject_of_le G B hia, totalProject_of_le G B hja]
      exact B.embed_trans i j a hij hja x
    · have haj : a ≤ j := le_of_lt (lt_of_not_ge hja)
      by_cases hia : i ≤ a
      · rw [totalProject_of_ge G B haj, totalProject_of_le G B hia]
        rw [← B.embed_trans i a j hia haj]
        exact B.project_retracts a j haj (B.embed i a hia x)
      · have hai : a ≤ i := le_of_lt (lt_of_not_ge hia)
        rw [totalProject_of_ge G B haj, totalProject_of_ge G B hai]
        exact B.project_embed a i j hai hij x
  contractive a i x := by
    by_cases hia : i ≤ a
    · rw [totalProject_of_le G B hia, (B.embed i a hia).norm_map]
    · rw [totalProject_of_ge G B (le_of_lt (lt_of_not_ge hia))]
      exact B.project_contractive a i _ x
  identityBelow i a hia x := totalProject_of_le G B hia x

end CoherentBiSystem

end ScottishBook155
