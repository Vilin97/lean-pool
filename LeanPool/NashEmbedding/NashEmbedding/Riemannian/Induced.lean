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
# The metric induced by an immersion into an inner-product space

For `u : M → E'` a smooth map with injective differential into a finite-dimensional
real inner-product space, the **induced metric** `g_x(v, w) := ⟪du_x v, du_x w⟫` is a
smooth Riemannian metric in Mathlib's sense (`ContMDiffRiemannianMetric`).  This is
the converse direction of `AmbientMetric.lean`, and it is what makes `nashCompact`
applicable to concrete manifolds: every sphere `Sⁿ ⊂ ℝⁿ⁺¹` with its round metric, and
any other submanifold of Euclidean space Mathlib provides.

Leaves L1–L4 (symmetry, positivity, von Neumann boundedness, section smoothness) were
proved by Aristotle (project c61ad094, 2026-08-30); `inducedMetric` packages them.
-/

open scoped Manifold ContDiff Topology
open Bundle Function ContinuousLinearMap Bornology Metric

noncomputable section

namespace NashEmbedding

section Induced

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']

/-- The induced bilinear form at `x`, on the model space `E`: `(v, w) ↦ ⟪du_x v, du_x w⟫`. -/
def inducedForm (u : M → E') (x : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  (innerBilin E').bilinearComp (diff (I := I) u x) (diff (I := I) u x)

/-- The same form, typed on the tangent space (definitional cast; an `abbrev` so that it
  unfolds to `inducedForm` reducibly). -/
abbrev inducedFormT (u : M → E') (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  show E →L[ℝ] E →L[ℝ] ℝ from inducedForm (I := I) u x

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] in
/-- **L1.** Symmetry. -/
theorem inducedForm_symm (u : M → E') (x : M) (v w : E) :
    inducedForm (I := I) u x v w = inducedForm (I := I) u x w v := by
  simp only [inducedForm, innerBilin, ContinuousLinearMap.bilinearComp_apply]
  exact real_inner_comm _ _

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] in
/-- Evaluation of the induced form. -/
theorem inducedForm_apply (u : M → E') (x : M) (v w : E) :
    inducedForm (I := I) u x v w = inner ℝ (diff (I := I) u x v) (diff (I := I) u x w) := rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] in
/-- Injectivity of `mfderiv` gives injectivity of the cast `diff`. -/
theorem diff_injective {u : M → E'} {x : M}
    (hinj : Injective (mfderiv I 𝓘(ℝ, E') u x)) : Injective (diff (I := I) u x) := by
  intro v w hvw
  exact hinj (show mfderiv I 𝓘(ℝ, E') u x v = mfderiv I 𝓘(ℝ, E') u x w from hvw)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] in
/-- **L2.** Positivity, from injectivity of the differential. -/
theorem inducedForm_pos {u : M → E'} {x : M}
    (hinj : Injective (mfderiv I 𝓘(ℝ, E') u x)) {v : E} (hv : v ≠ 0) :
    0 < inducedForm (I := I) u x v v := by
  rw [inducedForm_apply]
  refine real_inner_self_pos.2 fun h => hv ?_
  exact diff_injective hinj (by rw [h, map_zero])

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E'] in
/-- **L3.** The unit "ball" of the induced form is von Neumann bounded (all norms on a
  finite-dimensional space are equivalent; the form is positive definite). -/
theorem inducedForm_isVonNBounded {u : M → E'} {x : M}
    (hinj : Injective (mfderiv I 𝓘(ℝ, E') u x)) :
    IsVonNBounded ℝ {v : E | inducedForm (I := I) u x v v < 1} := by
  obtain ⟨K, hK, hanti⟩ :=
    LinearMap.exists_antilipschitzWith (diff (I := I) u x).toLinearMap
      (LinearMap.ker_eq_bot.2 (diff_injective hinj))
  refine Bornology.IsVonNBounded.subset (s₂ := Metric.ball (0 : E) ((K : ℝ) + 1)) ?_
    (NormedSpace.isVonNBounded_ball ℝ E ((K : ℝ) + 1))
  intro v hv
  have hv1 : inner ℝ (diff (I := I) u x v) (diff (I := I) u x v) < 1 := hv
  have hnorm : ‖diff (I := I) u x v‖ ^ 2 < 1 := by
    rwa [← real_inner_self_eq_norm_sq]
  have hlt : ‖diff (I := I) u x v‖ < 1 := by
    nlinarith [norm_nonneg (diff (I := I) u x v)]
  have hle : ‖v‖ ≤ (K : ℝ) * ‖diff (I := I) u x v‖ := by
    have := hanti.le_mul_dist v 0
    simpa [dist_eq_norm] using this
  have hKpos : (0:ℝ) < (K : ℝ) := by exact_mod_cast hK
  have : ‖v‖ < (K : ℝ) + 1 := by nlinarith [norm_nonneg (diff (I := I) u x v)]
  simpa [Metric.mem_ball, dist_eq_norm] using this

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- Evaluation of the induced form read in the trivialization at `x₀`
  (`hom_trivializationAt_apply`, `inCoordinates_apply_eq₂`). -/
theorem inducedForm_trivialization_apply (u : M → E') {x₀ x : M}
    (hx : x ∈ (chartAt H x₀).source) (a b : E) :
    (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀
        ⟨x, inducedFormT (I := I) u x⟩).2 a b =
      inducedForm (I := I) u x (tcoord I x₀ x a) (tcoord I x₀ x b) := by
  have hb : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by simpa using hx
  rw [hom_trivializationAt_apply, inCoordinates_apply_eq₂ hb hb (Set.mem_univ _)]
  simp
  rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- **L4.** Smoothness of the induced form as a section of the bundle of bilinear forms on
  `TM` (via `contMDiffAt_section`, `hom_trivializationAt_apply`, `inCoordinates_apply_eq₂`,
  and `contMDiffAt_inTangentCoordinates_mfderiv` / `inTangentCoordinates_mfderiv_eq` from
  `AmbientMetric.lean`). -/
theorem inducedForm_contMDiff {u : M → E'} (hu : ContMDiff I 𝓘(ℝ, E') ∞ u) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (inducedFormT (I := I) u x)) := by
  intro x₀
  rw [contMDiffAt_section]
  set Lt : M → E →L[ℝ] E' :=
    inTangentCoordinates I 𝓘(ℝ, E') id u (mfderiv I 𝓘(ℝ, E') u) x₀
  have hLtm : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E') ∞ Lt x₀ :=
    contMDiffAt_inTangentCoordinates_mfderiv hu x₀
  have hsmooth : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun x => (innerBilin E').bilinearComp (Lt x) (Lt x)) x₀ :=
    contMDiffAt_bilinearComp' (f := fun _ => innerBilin E') contMDiffAt_const hLtm hLtm
  refine hsmooth.congr_of_eventuallyEq ?_
  filter_upwards [chart_source_mem_nhds H x₀] with x hx
  have hLtx : Lt x = diff (I := I) u x ∘L tcoord I x₀ x := inTangentCoordinates_mfderiv_eq hx
  ext a b
  rw [inducedForm_trivialization_apply u hx, inducedForm_apply, hLtx]
  rfl

/-- The induced Riemannian metric of a smooth immersion `u : M → E'`. -/
def inducedMetric {u : M → E'} (hu : ContMDiff I 𝓘(ℝ, E') ∞ u)
    (hinj : ∀ x, Injective (mfderiv I 𝓘(ℝ, E') u x)) :
    ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _) where
  inner x := inducedFormT (I := I) u x
  symm x v w := inducedForm_symm (I := I) u x v w
  pos x v hv := inducedForm_pos (hinj x) hv
  isVonNBounded x := by
    change IsVonNBounded ℝ {v : E | inducedForm (I := I) u x v v < 1}
    exact inducedForm_isVonNBounded (hinj x)
  contMDiff := inducedForm_contMDiff hu

omit [FiniteDimensional ℝ E'] in
theorem inducedMetric_inner {u : M → E'} (hu : ContMDiff I 𝓘(ℝ, E') ∞ u)
    (hinj : ∀ x, Injective (mfderiv I 𝓘(ℝ, E') u x)) (x : M) (v w : E) :
    metricAt (inducedMetric hu hinj) x v w = inner ℝ (diff (I := I) u x v) (diff (I := I) u x w) :=
  rfl

end Induced

end NashEmbedding

end
