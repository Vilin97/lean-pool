/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/
module


/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request and direction of David Wiygul
-/
public import LeanPool.NashEmbedding.NashEmbedding.Compact.Main

/-!
# Solution to the Challenge

The declaration of `Challenge.lean`, proved.  It is a thin bridge to `NashEmbedding.nashCompact`;
the only difference is bookkeeping: the library states the pullback condition through the
predicate `PullsBackEuclidean`, whose definition unfolds to exactly the Challenge's clause
(`toEuclid` is the identity map exposing a tangent vector to Euclidean space as a point of it).

The underlying `NashEmbedding` development was substantially formalized by
Aristotle (Harmonic); see the repository provenance record.
-/

@[expose] public section

open scoped Manifold ContDiff
open Bundle

namespace NashEmbeddingTheorem

/-- **Nash's isometric embedding theorem**, proved in `NashEmbedding.nashCompact`.
Axioms: `propext`, `Classical.choice`, `Quot.sound`. -/
theorem nash_isometric_embedding
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M]
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) :
    ∃ (q : ℕ) (w : M → EuclideanSpace ℝ (Fin q)),
      ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ w ∧ Function.Injective w ∧
      ∀ (x : M) (v v' : TangentSpace I x),
        g.inner x v v' =
          @inner ℝ (EuclideanSpace ℝ (Fin q)) _
            (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) w x v)
            (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) w x v') :=
  let ⟨q, w, hw, hinj, hpull⟩ := NashEmbedding.nashCompact g
  ⟨q, w, hw, hinj, fun x v v' => hpull x v v'⟩

end NashEmbeddingTheorem
