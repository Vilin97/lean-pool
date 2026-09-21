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
import LeanPool.NashEmbedding.NashEmbedding.Riemannian.Pullback

/-!
# Round-sphere witnesses for `nashCompact`

Every unit sphere `Sⁿ ⊂ ℝⁿ⁺¹` with its round metric, and every product of round spheres
`Sⁿ × Sᵐ` with the product metric, isometrically embeds into Euclidean space via
`nashCompact`.
-/

open scoped Manifold ContDiff EuclideanSpace
open Bundle Function Metric

noncomputable section

namespace NashEmbedding

variable (n : ℕ)

/-- The round metric on `Sⁿ ⊂ ℝⁿ⁺¹`, induced by the inclusion. -/
def sphereMetric :
    ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → Type _) :=
  inducedMetric contMDiff_coe_sphere (fun v => mfderiv_coe_sphere_injective v)

/-- **Sⁿ.** Every round sphere isometrically embeds — via `nashCompact`. -/
theorem sphere_nashCompact :
    ∃ (q : ℕ) (w : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → EuclideanSpace ℝ (Fin q)),
      ContMDiff (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ w ∧ Injective w ∧
      PullsBackEuclidean (sphereMetric n) w :=
  nashCompact (sphereMetric n)

/-- **Sⁿ × Sᵐ.** Every product of round spheres, with the product metric, isometrically
  embeds — via `nashCompact` applied to `prodMetric`. -/
theorem sphereProd_nashCompact (n m : ℕ) :
    ∃ (q : ℕ) (w : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ×
        sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 → EuclideanSpace ℝ (Fin q)),
      ContMDiff ((𝓡 n).prod (𝓡 m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ w ∧ Injective w ∧
      PullsBackEuclidean (prodMetric (sphereMetric n) (sphereMetric m)) w :=
  nashCompact _

end NashEmbedding

end
