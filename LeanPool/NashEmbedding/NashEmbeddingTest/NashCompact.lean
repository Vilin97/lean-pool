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
import LeanPool.NashEmbedding.NashEmbedding.Riemannian.Induced
import LeanPool.NashEmbedding.NashEmbedding.Riemannian.Pullback
import LeanPool.NashEmbedding.NashEmbedding.Examples.FlatTorus
import LeanPool.NashEmbedding.NashEmbedding.Examples.Sphere
import LeanPool.NashEmbedding.NashEmbedding.Examples.Negative

/-!
# NashCompact witness compile-checks

Compile-time type checks that the general `nashCompact` / `sphere_nashCompact`
/ `sphereProd_nashCompact` / `torus2_matches_nashTorus` theorems specialize
cleanly to concrete instances (S¹, S², S³, S² × S³, Circle × Circle).
Guards against typeclass-resolution regressions that would only surface at
concrete manifolds.

Axiom guards for the top-level results live in `scripts/axioms.lean`; this
file has no `#print axioms` blocks.
-/

open scoped Manifold ContDiff

/-! ## Concrete manifolds: the round spheres -/

section Spheres
open Metric NashEmbedding

/-- **S¹.** The round circle isometrically embeds (via `nashCompact`). -/
example : ∃ (q : ℕ) (w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin q)),
    ContMDiff (𝓡 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ w ∧ Function.Injective w ∧
    PullsBackEuclidean (sphereMetric 1) w :=
  sphere_nashCompact 1

/-- **S².** -/
example : ∃ (q : ℕ) (w : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin q)),
    ContMDiff (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ w ∧ Function.Injective w ∧
    PullsBackEuclidean (sphereMetric 2) w :=
  sphere_nashCompact 2

/-- **S³.** -/
example : ∃ (q : ℕ) (w : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → EuclideanSpace ℝ (Fin q)),
    ContMDiff (𝓡 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ w ∧ Function.Injective w ∧
    PullsBackEuclidean (sphereMetric 3) w :=
  sphere_nashCompact 3

/-- **Negative.** A constant map into `ℝ⁵` does not pull the Euclidean metric back to the
    round metric on `S²`. -/
example (c : EuclideanSpace ℝ (Fin 5)) :
    ¬ PullsBackEuclidean (sphereMetric 2) (fun _ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 => c) :=
  haveI : Nonempty (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    ⟨⟨EuclideanSpace.single 0 1, by simp [PiLp.norm_single]⟩⟩
  not_pullsBackEuclidean_const (sphereMetric 2) c

/-- **S² × S³** with the product of the round metrics (via `prodMetric` and `nashCompact`). -/
example : ∃ (q : ℕ) (w : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ×
      sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → EuclideanSpace ℝ (Fin q)),
    ContMDiff ((𝓡 2).prod (𝓡 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ w ∧ Function.Injective w ∧
    PullsBackEuclidean (prodMetric (sphereMetric 2) (sphereMetric 3)) w :=
  sphereProd_nashCompact 2 3

end Spheres

/-! ## The flat torus: `nashCompact` meets `nashTorus` -/

section CrossCheck
open Metric NashEmbedding
open scoped NashEmbedding

/-- **Circle × Circle** with the flat product metric, through `nashCompact`. -/
example : ∃ (q : ℕ) (w : Circle × Circle → EuclideanSpace ℝ (Fin q)),
    ContMDiff ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ w ∧ Function.Injective w ∧
    PullsBackEuclidean flatTorus2Metric w :=
  nashCompact flatTorus2Metric

/-- **Cross-check.** The `nashCompact` embedding of `Circle × Circle`, composed with the
    universal cover `ℝ² → Circle × Circle`, is a witness for exactly the statement `nashTorus`
    proves directly for the flat metric on `ℝ²`. -/
example : IsInjRealizable (flatMetric 2) := torus2_matches_nashTorus

/-- … and here is the direct witness, for comparison. -/
example : IsInjRealizable (flatMetric 2) :=
  nashTorus (by norm_num) flatMetric_isPosDefSmoothMetric

end CrossCheck
