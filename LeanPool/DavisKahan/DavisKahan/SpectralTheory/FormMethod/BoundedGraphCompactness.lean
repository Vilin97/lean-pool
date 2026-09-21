/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import LeanPool.DavisKahan.DavisKahan.SpectralTheory.FormMethod.CompactGraphEmbedding
import Mathlib.Tactic

/-!
# Graph compactness under bounded perturbations

Adding a bounded operator does not change the domain of a closed operator and
produces an equivalent graph norm.  Therefore sequential compactness of the
ambient graph embedding is preserved in both directions.
-/

open Set Filter Topology
open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Abstract

noncomputable section

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- A graph-bounded sequence for `A + V` is graph-bounded for `A`. -/
theorem graph_bound_original_of_addBounded
    (A : H →ₗ.[𝕜] H)
    (V : H →L[𝕜] H)
    (x : ℕ → (TauCeti.LinearPMap.addBounded A V).domain)
    {C : ℝ}
    (hC : ∀ n,
      ‖(x n : H)‖ ^ 2 +
        ‖(TauCeti.LinearPMap.addBounded A V) (x n)‖ ^ 2 ≤ C) :
    ∃ D : ℝ, ∀ n,
      ‖(x n : H)‖ ^ 2 + ‖A (x n)‖ ^ 2 ≤ D := by
  change ℕ → A.domain at x
  let S := Real.sqrt (max C 0)
  refine ⟨S ^ 2 + ((1 + ‖V‖) * S) ^ 2, ?_⟩
  intro n
  have hx : ‖(x n : H)‖ ≤ S :=
    ambient_values_bounded_of_graph_bound (TauCeti.LinearPMap.addBounded A V) x hC n
  have hsum : ‖(TauCeti.LinearPMap.addBounded A V) (x n)‖ ≤ S :=
    operator_values_bounded_of_graph_bound (TauCeti.LinearPMap.addBounded A V) x hC n
  have hVx : ‖V (x n : H)‖ ≤ ‖V‖ * S :=
    (V.le_opNorm (x n : H)).trans
      (mul_le_mul_of_nonneg_left hx (norm_nonneg V))
  have hAeq : A (x n) =
      (TauCeti.LinearPMap.addBounded A V) (x n) - V (x n : H) := by
    change A (x n) =
      (A (x n) + V (x n : H)) - V (x n : H)
    abel
  have hAx : ‖A (x n)‖ ≤ (1 + ‖V‖) * S := by
    rw [hAeq]
    calc
      ‖(TauCeti.LinearPMap.addBounded A V) (x n) - V (x n : H)‖
          ≤ ‖(TauCeti.LinearPMap.addBounded A V) (x n)‖ + ‖V (x n : H)‖ :=
        norm_sub_le _ _
      _ ≤ S + ‖V‖ * S := add_le_add hsum hVx
      _ = (1 + ‖V‖) * S := by ring
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hfac : 0 ≤ (1 + ‖V‖) * S :=
    mul_nonneg (by positivity) hS
  have hx_sq : ‖(x n : H)‖ ^ 2 ≤ S ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hS).2 hx
  have hAx_sq : ‖A (x n)‖ ^ 2 ≤
      ((1 + ‖V‖) * S) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hfac).2 hAx
  exact add_le_add hx_sq hAx_sq

omit [CompleteSpace H] in
/-- A graph-bounded sequence for `A` is graph-bounded for `A + V`. -/
theorem graph_bound_addBounded_of_original
    (A : H →ₗ.[𝕜] H)
    (V : H →L[𝕜] H)
    (x : ℕ → A.domain)
    {C : ℝ}
    (hC : ∀ n,
      ‖(x n : H)‖ ^ 2 + ‖A (x n)‖ ^ 2 ≤ C) :
    ∃ D : ℝ, ∀ n,
      ‖(x n : H)‖ ^ 2 +
        ‖(TauCeti.LinearPMap.addBounded A V) (x n)‖ ^ 2 ≤ D := by
  change ℕ → (TauCeti.LinearPMap.addBounded A V).domain at x
  let S := Real.sqrt (max C 0)
  refine ⟨S ^ 2 + ((1 + ‖V‖) * S) ^ 2, ?_⟩
  intro n
  have hx : ‖(x n : H)‖ ≤ S :=
    ambient_values_bounded_of_graph_bound A x hC n
  have hAx : ‖A (x n)‖ ≤ S :=
    operator_values_bounded_of_graph_bound A x hC n
  have hVx : ‖V (x n : H)‖ ≤ ‖V‖ * S :=
    (V.le_opNorm (x n : H)).trans
      (mul_le_mul_of_nonneg_left hx (norm_nonneg V))
  have hsum : ‖(TauCeti.LinearPMap.addBounded A V) (x n)‖ ≤
      (1 + ‖V‖) * S := by
    change ‖A (x n) + V (x n : H)‖ ≤
      (1 + ‖V‖) * S
    calc
      ‖A (x n) + V (x n : H)‖
          ≤ ‖A (x n)‖ + ‖V (x n : H)‖ := norm_add_le _ _
      _ ≤ S + ‖V‖ * S := add_le_add hAx hVx
      _ = (1 + ‖V‖) * S := by ring
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hfac : 0 ≤ (1 + ‖V‖) * S :=
    mul_nonneg (by positivity) hS
  have hx_sq : ‖(x n : H)‖ ^ 2 ≤ S ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hS).2 hx
  have hsum_sq : ‖(TauCeti.LinearPMap.addBounded A V) (x n)‖ ^ 2 ≤
      ((1 + ‖V‖) * S) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hfac).2 hsum
  exact add_le_add hx_sq hsum_sq

omit [CompleteSpace H] in
/-- Sequential graph compactness is preserved by a bounded perturbation. -/
theorem graphCompact_addBounded
    (A : H →ₗ.[𝕜] H)
    (V : H →L[𝕜] H)
    (hA : SequentiallyCompactGraphEmbedding A) :
    SequentiallyCompactGraphEmbedding (TauCeti.LinearPMap.addBounded A V) := by
  intro x hx
  obtain ⟨C, hC⟩ := hx
  obtain ⟨D, hD⟩ := graph_bound_original_of_addBounded A V x hC
  exact hA x ⟨D, hD⟩

omit [CompleteSpace H] in
/-- Sequential graph compactness of a bounded perturbation implies graph
compactness of the original operator. -/
theorem graphCompact_of_addBounded
    (A : H →ₗ.[𝕜] H)
    (V : H →L[𝕜] H)
    (hAV : SequentiallyCompactGraphEmbedding (TauCeti.LinearPMap.addBounded A V)) :
    SequentiallyCompactGraphEmbedding A := by
  intro x hx
  obtain ⟨C, hC⟩ := hx
  obtain ⟨D, hD⟩ := graph_bound_addBounded_of_original A V x hC
  exact hAV x ⟨D, hD⟩

omit [CompleteSpace H] in
/-- Bounded perturbations preserve sequential graph compactness exactly. -/
theorem graphCompact_addBounded_iff
    (A : H →ₗ.[𝕜] H)
    (V : H →L[𝕜] H) :
    SequentiallyCompactGraphEmbedding (TauCeti.LinearPMap.addBounded A V) ↔
      SequentiallyCompactGraphEmbedding A := by
  constructor
  · exact graphCompact_of_addBounded A V
  · exact graphCompact_addBounded A V

end

end Abstract
end FreeBeam
end DavisKahan
end TauCeti
