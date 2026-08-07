/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Path.LocalPrimitive
import LeanPool.JacobianDiffgeo.Path.Continuation

/-!
# The in-chart segment path (shared helper for §6.3/§6.5)

Unit: period-lattice-rank. The straight-segment path inside a chart-ball, pulled back through the
chart: used by both `Nondegeneracy.lean` (§5.1 step 2) and `Discreteness.lean` (Stage C.2) to
compute a path integral of `η` as the difference of a local primitive's values. Factored out once
since both sites need exactly the same construction (design §6.5's `segmentPath` note).

Main declarations: `RS.segmentPath`, `RS.pathIntegral_segmentPath`.
-/

open scoped ContDiff Manifold
open Set Metric unitInterval

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The straight segment from `e p` to `e q` inside `ball c r ⊆ e.target`, pulled back through the
chart `e` — a genuine continuous path `p ⤳ q` (the whole segment stays inside the ball by
convexity, where `e.symm` is continuous). Needs `p, q` inside the chart's source so the endpoints
come out right. -/
noncomputable def segmentPath {e : OpenPartialHomeomorph X ℂ} {c : ℂ} {r : ℝ}
    (hballsub : ball c r ⊆ e.target) {p q : X} (hp_src : p ∈ e.source) (hq_src : q ∈ e.source)
    (hp : e p ∈ ball c r) (hq : e q ∈ ball c r) :
    Path p q where
  toFun t := e.symm (AffineMap.lineMap (e p) (e q) (t : ℝ))
  continuous_toFun := by
    apply ContinuousOn.comp_continuous (e.continuousOn_symm) (by fun_prop)
    intro t
    exact hballsub ((convex_ball c r).lineMap_mem hp hq t.2)
  source' := by
    show e.symm (AffineMap.lineMap (e p) (e q) ((0 : I) : ℝ)) = p
    have : ((0 : I) : ℝ) = 0 := rfl
    rw [this, AffineMap.lineMap_apply_zero]
    exact e.left_inv hp_src
  target' := by
    show e.symm (AffineMap.lineMap (e p) (e q) ((1 : I) : ℝ)) = q
    have : ((1 : I) : ℝ) = 1 := rfl
    rw [this, AffineMap.lineMap_apply_one]
    exact e.left_inv hq_src

/-- The path integral of `η` along `segmentPath` is the difference of a local primitive's values,
via the constant-chart cell primitive (`isPrimitiveAlongMap_of_ball`) and well-definedness
(`IsPrimitiveAlong.pathIntegral_eq`). -/
theorem pathIntegral_segmentPath {η : Form1 X} {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) {c : ℂ} {r : ℝ}
    (hballsub : ball c r ⊆ e.target) {p q : X} (hp_src : p ∈ e.source) (hq_src : q ∈ e.source)
    (hp : e p ∈ ball c r) (hq : e q ∈ ball c r)
    {g : ℂ → ℂ} (hg : ∀ z ∈ ball c r, HasDerivAt g (coeffIn e η z) z) :
    pathIntegral (segmentPath hballsub hp_src hq_src hp hq) η = g (e q) - g (e p) := by
  have hprim : IsPrimitiveAlong (segmentPath hballsub hp_src hq_src hp hq) η
      (fun t => g (e ((segmentPath hballsub hp_src hq_src hp hq).extend t))) := by
    apply isPrimitiveAlongMap_of_ball he hg
    intro a _
    set t : I := projIcc 0 1 zero_le_one a with ht_def
    have htIcc : (t : ℝ) ∈ Icc (0 : ℝ) 1 := t.2
    have hballmem : AffineMap.lineMap (e p) (e q) (t : ℝ) ∈ ball c r :=
      (convex_ball c r).lineMap_mem hp hq htIcc
    have hextend : (segmentPath hballsub hp_src hq_src hp hq).extend a
        = e.symm (AffineMap.lineMap (e p) (e q) (t : ℝ)) := rfl
    refine ⟨?_, ?_⟩
    · rw [hextend]; exact e.map_target (hballsub hballmem)
    · rw [hextend, e.right_inv (hballsub hballmem)]; exact hballmem
  rw [hprim.pathIntegral_eq, (segmentPath hballsub hp_src hq_src hp hq).extend_one,
    (segmentPath hballsub hp_src hq_src hp hq).extend_zero]

end RS

end
