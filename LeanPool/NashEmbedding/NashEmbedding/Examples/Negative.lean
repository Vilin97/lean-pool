/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/

/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import LeanPool.NashEmbedding.NashEmbedding.Compact.Main

/-!
# A negative witness for `PullsBackEuclidean`

On a nonempty manifold with positive-dimensional model space, a constant map into
Euclidean space cannot pull the Euclidean inner product back to a Riemannian metric —
its differential is zero, so the pullback is degenerate.
-/

open scoped Manifold ContDiff
open Bundle Function

noncomputable section

namespace NashEmbedding

/-- A constant map never pulls the Euclidean metric back to a Riemannian metric
  (when the manifold has positive dimension and a point). -/
theorem not_pullsBackEuclidean_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
     [Nontrivial E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [Nonempty M]
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {q : ℕ} (c : EuclideanSpace ℝ (Fin q)) :
    ¬ PullsBackEuclidean g (fun _ : M => c) := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty M›
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hpos := g.pos x v hv
  have h0 : mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) (fun _ : M => c) x v = 0 := by
    rw [mfderiv_const]; rfl
  have := h x v v
  rw [h0] at this
  simp only [toEuclid] at this
  exact absurd (this.trans (inner_zero_left _)) hpos.ne'

end NashEmbedding

end
