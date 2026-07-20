/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# `RellichKondrachov.Geometry.Manifold.Riemannian.ChartLocalLipschitz`

Local Lipschitz control for Riemannian charts.

This file extracts a reusable lemma showing that, around any point `x : M`, the inverse extended
chart `(extChartAt I x).symm` is Lipschitz on a small ball in chart coordinates (with respect to the
Riemannian `edist` on `M`).

## Main result

- `RellichKondrachov.Geometry.Manifold.Riemannian.`
  `lipschitzOnWith_symm_extChartAt_ofRiemannianMetric`
-/

namespace RellichKondrachov
namespace Geometry
namespace Manifold
namespace Riemannian

open Set Filter MeasureTheory
open _root_.Manifold _root_.Bundle
open scoped NNReal ENNReal Topology Manifold

local notation "n∞" => (⊤ : WithTop ℕ∞)

section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I n∞ M] [IsManifold I (1 : WithTop ℕ∞) M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-!
`mfderivWithin` is a continuous linear map between tangent spaces. For the model
space `E` (viewed as a manifold), we locally activate the
`NormedAddCommGroup`/`NormedSpace` structures on its tangent
spaces so that operator-norm estimates are available.

This matches the approach used in Mathlib’s Riemannian manifold development: these instances should
not be global because they need not coincide definitionally with Riemannian structures.
-/

@[reducible]
private noncomputable def normedAddCommGroupTangentSpaceVectorSpace (x : E) :
    NormedAddCommGroup (TangentSpace (𝓘(ℝ, E)) x) :=
  inferInstanceAs (NormedAddCommGroup E)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace

@[reducible]
private noncomputable def normedSpaceTangentSpaceVectorSpace (x : E) :
    NormedSpace ℝ (TangentSpace (𝓘(ℝ, E)) x) :=
  inferInstanceAs (NormedSpace ℝ E)

attribute [local instance] normedSpaceTangentSpaceVectorSpace

omit [FiniteDimensional ℝ E] [IsManifold I n∞ M] in
/-- Around any point `x`, the inverse extended chart is Lipschitz on a small ball in chart
coordinates, with respect to the Riemannian distance. -/
theorem lipschitzOnWith_symm_extChartAt_ofRiemannianMetric
    [EMetricSpace M] [IsRiemannianManifold I M] (x : M) :
    ∃ (C : ℝ≥0), 0 < C ∧ ∃ (r : ℝ), 0 < r ∧
      LipschitzOnWith C (extChartAt I x).symm (Metric.ball (extChartAt I x x) r ∩ range I) := by
  classical
  -- Prefer the `ContinuousLinearMap`-native `SeminormedAddCommGroup` structure on `→L` spaces to
  -- avoid definitional mismatches between `‖_‖ₑ` occurrences.
  letI (y : E) :
      SeminormedAddCommGroup
        (TangentSpace (𝓘(ℝ, E)) y →L[ℝ] TangentSpace I ((extChartAt I x).symm y)) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  -- Start from a local bound on the derivative of `(extChartAt I x).symm`.
  rcases eventually_enorm_mfderivWithin_symm_extChartAt_lt (I := I) x with ⟨C, C_pos, hC⟩
  refine ⟨C, C_pos, ?_⟩
  let P : Set E :=
    {y | ‖mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) y‖ₑ < C}
  have hP : P ∈ 𝓝[range I] (extChartAt I x x) := by
    change (∀ᶠ y in 𝓝[range I] (extChartAt I x x), y ∈ P)
    filter_upwards [hC] with y hy
    change ‖mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) y‖ₑ < (C : ℝ≥0∞)
    exact hy
  -- Choose a small convex neighborhood in the chart where the derivative
  -- bound holds and the map is defined.
  obtain ⟨r, r_pos, hr⟩ : ∃ r > 0,
      Metric.ball (extChartAt I x x) r ∩ range I ⊆ (extChartAt I x).target ∩ P := by
    exact Metric.mem_nhdsWithin_iff.1 (inter_mem (extChartAt_target_mem_nhdsWithin (I := I) x) hP)
  refine ⟨r, r_pos, ?_⟩
  -- Prove the Lipschitz inequality pointwise on the chosen set.
  refine fun y₁ hy₁ y₂ hy₂ => ?_
  -- Construct the segment path in chart coordinates and push it forward by `(extChartAt I x).symm`.
  let η := ContinuousAffineMap.lineMap (R := ℝ) y₁ y₂
  let γ : ℝ → M := (extChartAt I x).symm ∘ η
  have hη : Icc (0 : ℝ) 1 ⊆ ⇑η ⁻¹' ((extChartAt I x).target ∩ P) := by
    -- The image of the segment lies in the controlled chart neighborhood.
    simp only [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq, ← segment_eq_image_lineMap,
      η]
    refine (Subset.trans ?_ hr)
    have hy₁' : y₁ ∈ Metric.ball (extChartAt I x x) r ∩ range I := hy₁
    have hy₂' : y₂ ∈ Metric.ball (extChartAt I x x) r ∩ range I := hy₂
    exact ((convex_ball (extChartAt I x x) r).inter I.convex_range).segment_subset hy₁' hy₂'
  simp only [preimage_inter, subset_inter_iff] at hη
  have η_smooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 η (Icc (0 : ℝ) 1) := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  -- Bound the Riemannian distance by the length of this explicit path.
  have hdist :
      riemannianEDist I ((extChartAt I x).symm y₁) ((extChartAt I x).symm y₂) ≤
        pathELength I γ 0 1 := by
    apply riemannianEDist_le_pathELength (I := I) (γ := γ) (a := 0) (b := 1) (hab := zero_le_one)
    · exact (contMDiffOn_extChartAt_symm (I := I) x).comp η_smooth hη.1
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
  -- Finally, control the length of `γ` thanks to the boundedness of the derivative of
  -- `(extChartAt I x).symm` on the whole controlled set.
  have hlen : pathELength I γ 0 1 ≤ C * edist y₁ y₂ := by
    rw [← lintegral_fderiv_lineMap_eq_edist, pathELength_eq_lintegral_mfderivWithin_Icc,
      ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    apply setLIntegral_mono' measurableSet_Icc (fun t ht ↦ ?_)
    have :
        mfderivWithin 𝓘(ℝ) I γ (Icc (0 : ℝ) 1) t =
          (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) (η t)) ∘L
            (mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) η (Icc (0 : ℝ) 1) t) := by
      apply mfderivWithin_comp
      · exact mdifferentiableWithinAt_extChartAt_symm (I := I) (x := x) (hη.1 ht)
      · exact η_smooth.mdifferentiableOn one_ne_zero t ht
      · exact hη.1.trans (preimage_mono (extChartAt_target_subset_range (I := I) x))
      · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
        exact uniqueDiffOn_Icc zero_lt_one t ht
    have :
        mfderivWithin 𝓘(ℝ) I γ (Icc (0 : ℝ) 1) t 1 =
          (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) (η t))
            (mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) η (Icc (0 : ℝ) 1) t 1) :=
      congr($this 1)
    rw [this]
    apply (ContinuousLinearMap.le_opNorm_enorm _ _).trans
    gcongr
    · have htP : η t ∈ P := by
        have : t ∈ ⇑η ⁻¹' P := hη.2 ht
        simpa [Set.mem_preimage] using this
      have hbound :
          ‖mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) (η t)‖ₑ < (C : ℝ≥0∞) := by
        change η t ∈ P
        exact htP
      exact hbound.le
    · simp only [mfderivWithin_eq_fderivWithin]
      exact le_of_eq rfl
  -- Finish the Lipschitz inequality by rewriting `edist` on `M` as `riemannianEDist`.
  simpa [IsRiemannianManifold.out (I := I) (M := M)] using (hdist.trans hlen)

end

end Riemannian
end Manifold
end Geometry
end RellichKondrachov
