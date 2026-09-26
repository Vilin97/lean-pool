/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.ChartNormBounds
public import LeanPool.PoincareGeometry.AlmostSchur.ConnectionCoordinates

/-!
# Unlocalized chart derivative bounds

The constant depends only on a chart and a compact subset of its target, not on
the scalar function. There is no cutoff and no function-value or L²-function term.
We use the proved `exists_bound_tangentChart_symmL` on the inverse image of the
compact set, `fderiv_chart_comp`, and the Riesz norm identity `norm_gradient`.
The operator estimate is Mathlib's `ContinuousLinearMap.opNorm_comp_le`.
-/

@[expose] public noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]

variable [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]

/-- A fixed compact chart target has a uniform operator-norm derivative bound by
the intrinsic gradient, simultaneously for all C¹ scalar functions. -/
theorem exists_norm_fderiv_chart_comp_le (c : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (f : M → ℝ), ContMDiff I 𝓘(ℝ, ℝ) 1 f →
      ∀ z ∈ K, ‖fderiv ℝ (f ∘ (extChartAt I c).symm) z‖ ≤
        B * ‖gradient (I := I) f ((extChartAt I c).symm z)‖ := by
  let φ := extChartAt I c
  have hi : IsCompact (φ.symm '' K) :=
    hK.image_of_continuousOn ((continuousOn_extChartAt_symm c).mono hKt)
  have his : φ.symm '' K ⊆ (chartAt H c).source := by
    rintro x ⟨z, hz, rfl⟩
    simpa only [φ, extChartAt_source] using φ.map_target (hKt hz)
  obtain ⟨B, hB0, hB⟩ := exists_bound_tangentChart_symmL (I := I) c hi his
  refine ⟨B, hB0, fun f hf z hz => ?_⟩
  have hzT : z ∈ φ.target := hKt hz
  have hx : φ.symm z ∈ (chartAt H c).source := his ⟨z, hz, rfl⟩
  have hcoord : fderiv ℝ (f ∘ φ.symm) z =
      (mvfderiv I f (φ.symm z)).comp
        ((trivializationAt E (TangentSpace I) c).symmL ℝ (φ.symm z)) := by
    ext v
    have h := fderiv_chart_comp f c (φ.symm z) hx
      (hf.mdifferentiableAt (by norm_num)) v
    change fderiv ℝ (f ∘ φ.symm) (φ (φ.symm z)) v = _ at h
    simpa only [φ.right_inv hzT, ContinuousLinearMap.comp_apply] using h
  rw [hcoord, norm_gradient]
  calc
    _ ≤ ‖mvfderiv I f (φ.symm z)‖ *
        ‖(trivializationAt E (TangentSpace I) c).symmL ℝ (φ.symm z)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖mvfderiv I f (φ.symm z)‖ * B :=
      mul_le_mul_of_nonneg_left (hB _ ⟨z, hz, rfl⟩) (norm_nonneg (mvfderiv I f (φ.symm z)))
    _ = B * ‖mvfderiv I f (φ.symm z)‖ := mul_comm _ _

/-- Unlocalized directional derivative control on a compact chart target. In
particular, the right-hand side has no cutoff derivative or function-value term. -/
theorem exists_abs_fderiv_chart_comp_apply_le (c : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (f : M → ℝ), ContMDiff I 𝓘(ℝ, ℝ) 1 f →
      ∀ z ∈ K, ∀ v : E, |fderiv ℝ (f ∘ (extChartAt I c).symm) z v| ≤
        B * ‖v‖ * ‖gradient (I := I) f ((extChartAt I c).symm z)‖ := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_fderiv_chart_comp_le c hK hKt
  refine ⟨B, hB0, fun f hf z hz v => ?_⟩
  calc
    _ ≤ ‖fderiv ℝ (f ∘ (extChartAt I c).symm) z‖ * ‖v‖ :=
      (fderiv ℝ (f ∘ (extChartAt I c).symm) z).le_opNorm v
    _ ≤ (B * ‖gradient (I := I) f ((extChartAt I c).symm z)‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (hB f hf z hz) (norm_nonneg v)
    _ = _ := by ring

end AlmostSchur
