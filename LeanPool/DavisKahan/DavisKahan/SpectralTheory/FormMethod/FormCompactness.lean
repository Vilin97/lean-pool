/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module


public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.FormMethod.CoerciveFormResolvent
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.FormMethod.CompactGraphEmbedding
public import Mathlib.Tactic

/-!
# Compact form embeddings give compact resolvents

Rellich compactness enters the form method through the embedding `j : V → H`.
If `j` sends bounded sequences in the form space to sequences with ambiently
Cauchy subsequences, then the variational resolvent `j A⁻¹ j*` is compact in
the same sequential sense.  Consequently the associated unbounded operator
has compact graph embedding.
-/

@[expose] public section

open Set Filter Topology
open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Abstract

noncomputable section

universe u v

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
variable {V : Type v} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [CompleteSpace V]

/-- Sequential compactness of a continuous embedding on bounded sequences. -/
def SequentiallyCompactEmbedding (j : V →L[𝕜] H) : Prop :=
  ∀ u : ℕ → V,
    (∃ C : ℝ, ∀ n, ‖u n‖ ≤ C) →
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      CauchySeq (fun n => j (u (phi n)))

omit [CompleteSpace H] in
/-- A bounded operator maps bounded sequences to bounded sequences. -/
theorem bounded_sequence_comp
    {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (T : H →L[𝕜] W) (x : ℕ → H)
    {C : ℝ} (hC : ∀ n, ‖x n‖ ≤ C) :
    ∃ D : ℝ, ∀ n, ‖T (x n)‖ ≤ D := by
  refine ⟨‖T‖ * max C 0, ?_⟩
  intro n
  exact (T.le_opNorm (x n)).trans
    (mul_le_mul_of_nonneg_left
      ((hC n).trans (le_max_left _ _)) (norm_nonneg T))

/-- Compactness of the form embedding implies compactness of the ambient
variational resolvent. -/
theorem CoerciveFormData.resolvent_sequentiallyCompact
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V))
    (hcompact : SequentiallyCompactEmbedding D.embed) :
    SequentiallyCompactOperator D.resolvent := by
  intro f hf
  obtain ⟨C, hC⟩ := hf
  have hubounded : ∃ B : ℝ, ∀ n, ‖D.solutionOperator (f n)‖ ≤ B :=
    bounded_sequence_comp D.solutionOperator f hC
  obtain ⟨phi, hphi, hcauchy⟩ :=
    hcompact (fun n => D.solutionOperator (f n)) hubounded
  exact ⟨phi, hphi, hcauchy⟩

/-- A compact form embedding gives compact graph embedding for the associated
positive self-adjoint operator. -/
theorem CoerciveFormData.associatedOperator_graph_compact
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V))
    (hcompact : SequentiallyCompactEmbedding D.embed) :
    SequentiallyCompactGraphEmbedding D.associatedOperator := by
  exact inverse_graph_embedding_compact
    D.resolvent D.resolvent_isSelfAdjoint D.resolvent_injective
    (D.resolvent_sequentiallyCompact hcompact)

/-- For the form realization, compactness of the ambient resolvent and the
inverse graph embedding are equivalent. -/
theorem CoerciveFormData.graph_compact_iff_resolvent_compact
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    SequentiallyCompactGraphEmbedding D.associatedOperator ↔
      SequentiallyCompactOperator D.resolvent := by
  exact inverse_graph_compact_iff
    D.resolvent D.resolvent_isSelfAdjoint D.resolvent_injective

end

end Abstract
end FreeBeam
end DavisKahan
end TauCeti
