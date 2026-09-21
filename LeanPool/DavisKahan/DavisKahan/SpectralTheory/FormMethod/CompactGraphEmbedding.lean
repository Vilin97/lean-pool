/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import LeanPool.DavisKahan.DavisKahan.SpectralTheory.FormMethod.BoundedInverseRealization
import Mathlib.Tactic

/-!
# Compact resolvents and compact graph embeddings

The Section 9 analytic interface currently states compactness sequentially:
graph-bounded sequences in the free-beam domain have ambiently Cauchy
subsequences.  A variational construction instead produces a compact bounded
solution operator `R`, whose inverse is the shifted beam operator.

This file proves the exact bridge in both directions.  It deliberately uses a
small sequential compactness predicate so the result does not depend on a
particular bundled compact-operator API.
-/

open scoped InnerProductSpace
open Set Filter Topology

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Abstract

noncomputable section

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- Sequential compactness on bounded sequences for a bounded operator. -/
def SequentiallyCompactOperator (R : H →L[𝕜] H) : Prop :=
  ∀ y : ℕ → H,
    (∃ C : ℝ, ∀ n, ‖y n‖ ≤ C) →
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      CauchySeq (fun n => R (y (phi n)))

/-- Sequential compactness of the ambient embedding of a closed-operator graph
 domain.  This matches the shape used by `SobolevTraceFoundation.graph_compact`.
-/
def SequentiallyCompactGraphEmbedding
    (A : H →ₗ.[𝕜] H) : Prop :=
  ∀ x : ℕ → A.domain,
    (∃ C : ℝ, ∀ n,
      ‖(x n : H)‖ ^ 2 + ‖A (x n)‖ ^ 2 ≤ C) →
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      CauchySeq (fun n => ((x (phi n) : A.domain) : H))

omit [CompleteSpace H] in
/-- A sum-of-squares graph bound gives a uniform bound on operator values. -/
theorem operator_values_bounded_of_graph_bound
    (A : H →ₗ.[𝕜] H)
    (x : ℕ → A.domain) {C : ℝ}
    (hC : ∀ n,
      ‖(x n : H)‖ ^ 2 + ‖A (x n)‖ ^ 2 ≤ C) :
    ∀ n, ‖A (x n)‖ ≤ Real.sqrt (max C 0) := by
  intro n
  have hsquare : ‖A (x n)‖ ^ 2 ≤ max C 0 := by
    have hnonneg : 0 ≤ ‖(x n : H)‖ ^ 2 := sq_nonneg _
    have hle : ‖A (x n)‖ ^ 2 ≤ C := by
      linarith [hC n]
    exact hle.trans (le_max_left _ _)
  exact Real.le_sqrt_of_sq_le hsquare

omit [CompleteSpace H] in
/-- A sum-of-squares graph bound gives a uniform bound on ambient values. -/
theorem ambient_values_bounded_of_graph_bound
    (A : H →ₗ.[𝕜] H)
    (x : ℕ → A.domain) {C : ℝ}
    (hC : ∀ n,
      ‖(x n : H)‖ ^ 2 + ‖A (x n)‖ ^ 2 ≤ C) :
    ∀ n, ‖(x n : H)‖ ≤ Real.sqrt (max C 0) := by
  intro n
  have hsquare : ‖(x n : H)‖ ^ 2 ≤ max C 0 := by
    have hnonneg : 0 ≤ ‖A (x n)‖ ^ 2 := sq_nonneg _
    have hle : ‖(x n : H)‖ ^ 2 ≤ C := by
      linarith [hC n]
    exact hle.trans (le_max_left _ _)
  exact Real.le_sqrt_of_sq_le hsquare

/-- Compactness of a bounded resolvent implies compactness of the ambient
 embedding of its inverse graph domain. -/
theorem inverse_graph_embedding_compact
    (R : H →L[𝕜] H) (hR : IsSelfAdjoint R)
    (hinj : Function.Injective R)
    (hcompact : SequentiallyCompactOperator R) :
    SequentiallyCompactGraphEmbedding (inversePartialMap R hR hinj) := by
  intro x hx
  obtain ⟨C, hC⟩ := hx
  let y : ℕ → H := fun n =>
    (inversePartialMap R hR hinj) (x n)
  have hybounded : ∃ D : ℝ, ∀ n, ‖y n‖ ≤ D := by
    refine ⟨Real.sqrt (max C 0), ?_⟩
    exact operator_values_bounded_of_graph_bound
      (inversePartialMap R hR hinj) x hC
  obtain ⟨phi, hphi, hcauchy⟩ := hcompact y hybounded
  refine ⟨phi, hphi, ?_⟩
  have heq : (fun n => R (y (phi n))) =
      fun n => ((x (phi n) : (inversePartialMap R hR hinj).domain) : H) := by
    funext n
    exact R_inversePartialMap_apply R hR hinj (x (phi n))
  rwa [heq] at hcauchy

/-- A uniform bound on `y` gives a graph bound for the inverse-domain sequence
 `R y`. -/
theorem graph_bound_of_bounded_preimage
    (R : H →L[𝕜] H) (hR : IsSelfAdjoint R)
    (hinj : Function.Injective R)
    (y : ℕ → H) {C : ℝ} (hC : ∀ n, ‖y n‖ ≤ C) :
    ∀ n,
      ‖((⟨R (y n), LinearMap.mem_range_self R.toLinearMap (y n)⟩ :
          (inversePartialMap R hR hinj).domain) : H)‖ ^ 2 +
        ‖(inversePartialMap R hR hinj)
          ⟨R (y n), LinearMap.mem_range_self R.toLinearMap (y n)⟩‖ ^ 2
      ≤ (‖R‖ ^ 2 + 1) * max C 0 ^ 2 := by
  intro n
  have hCn : ‖y n‖ ≤ max C 0 :=
    (hC n).trans (le_max_left _ _)
  have hRyn : ‖R (y n)‖ ≤ ‖R‖ * max C 0 :=
    (R.le_opNorm (y n)).trans
      (mul_le_mul_of_nonneg_left hCn (norm_nonneg R))
  rw [inversePartialMap_apply_R]
  change ‖R (y n)‖ ^ 2 + ‖y n‖ ^ 2 ≤
    (‖R‖ ^ 2 + 1) * max C 0 ^ 2
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hR0 : 0 ≤ ‖R‖ := norm_nonneg _
  have hRyn_sq : ‖R (y n)‖ ^ 2 ≤ (‖R‖ * max C 0) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR0 hC0)).2 hRyn
  have hyn_sq : ‖y n‖ ^ 2 ≤ max C 0 ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hC0).2 hCn
  calc
    ‖R (y n)‖ ^ 2 + ‖y n‖ ^ 2
        ≤ (‖R‖ * max C 0) ^ 2 + max C 0 ^ 2 :=
      add_le_add hRyn_sq hyn_sq
    _ = (‖R‖ ^ 2 + 1) * max C 0 ^ 2 := by ring

/-- Compactness of the inverse graph embedding implies sequential compactness
 of the bounded resolvent. -/
theorem compact_of_inverse_graph_embedding_compact
    (R : H →L[𝕜] H) (hR : IsSelfAdjoint R)
    (hinj : Function.Injective R)
    (hgraph : SequentiallyCompactGraphEmbedding
      (inversePartialMap R hR hinj)) :
    SequentiallyCompactOperator R := by
  intro y hy
  obtain ⟨C, hC⟩ := hy
  let x : ℕ → (inversePartialMap R hR hinj).domain := fun n =>
    ⟨R (y n), LinearMap.mem_range_self R.toLinearMap (y n)⟩
  have hxbound : ∃ D : ℝ, ∀ n,
      ‖(x n : H)‖ ^ 2 +
        ‖(inversePartialMap R hR hinj) (x n)‖ ^ 2 ≤ D := by
    refine ⟨(‖R‖ ^ 2 + 1) * max C 0 ^ 2, ?_⟩
    exact graph_bound_of_bounded_preimage R hR hinj y hC
  obtain ⟨phi, hphi, hcauchy⟩ := hgraph x hxbound
  refine ⟨phi, hphi, ?_⟩
  exact hcauchy

/-- For inverse realizations, bounded-resolvent compactness and graph-embedding
 compactness are equivalent in the sequential formulation. -/
theorem inverse_graph_compact_iff
    (R : H →L[𝕜] H) (hR : IsSelfAdjoint R)
    (hinj : Function.Injective R) :
    SequentiallyCompactGraphEmbedding (inversePartialMap R hR hinj) ↔
      SequentiallyCompactOperator R := by
  constructor
  · exact compact_of_inverse_graph_embedding_compact R hR hinj
  · exact inverse_graph_embedding_compact R hR hinj

end

end Abstract
end FreeBeam
end DavisKahan
end TauCeti
