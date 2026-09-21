/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.EnergyChartDerivative

/-! # Compact cutoff of an actual coordinate function -/

@[expose] public noncomputable section
open Set Bundle
open scoped Manifold ContDiff Topology
namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]

/-- Multiplication by a coordinate cutoff; no uncut chart extension is asserted smooth. -/
def chartCutoff (c : M) (χ : E → ℝ) (f : M → ℝ) : E → ℝ :=
  fun z => χ z * f ((extChartAt I c).symm z)

omit [IsManifold I ∞ M] [I.Boundaryless] in
/-- Localization does not enlarge support. -/
theorem tsupport_chartCutoff_subset (c : M) (χ : E → ℝ) (f : M → ℝ) :
    tsupport (chartCutoff (I := I) c χ f) ⊆ tsupport χ :=
  tsupport_mul_subset_left

/-- A compact cutoff inside the chart gives a genuine global C¹ Euclidean test. -/
theorem contDiff_chartCutoff (c : M) {χ : E → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hs : tsupport χ ⊆ (extChartAt I c).target)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) :
    ContDiff ℝ 1 (chartCutoff (I := I) c χ f) := by
  have hf' : ContDiffOn ℝ 1 (f ∘ (extChartAt I c).symm) (extChartAt I c).target := by
    apply ContMDiffOn.contDiffOn
    exact hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm c)
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport χ
  · exact hχ.contDiffAt.mul
      (hf'.contDiffAt
        ((isOpen_extChartAt_target (I := I) c).mem_nhds (hs hz)))
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hz] with y hy
    simp [chartCutoff, image_eq_zero_of_notMem_tsupport hy]

omit [IsManifold I ∞ M] [I.Boundaryless] in
/-- The localized coordinate function has compact support. -/
theorem hasCompactSupport_chartCutoff (c : M) {χ : E → ℝ}
    (hc : HasCompactSupport χ) (f : M → ℝ) :
    HasCompactSupport (chartCutoff (I := I) c χ f) := hc.mul_right

/-- The actual product rule, on the chart target. -/
theorem fderiv_chartCutoff (c : M) {χ : E → ℝ} (hχ : ContDiff ℝ 1 χ)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) {z : E}
    (hz : z ∈ (extChartAt I c).target) (v : E) :
    fderiv ℝ (chartCutoff (I := I) c χ f) z v =
      fderiv ℝ χ z v * f ((extChartAt I c).symm z) +
        χ z * fderiv ℝ (f ∘ (extChartAt I c).symm) z v := by
  have hf' : ContDiffOn ℝ 1 (f ∘ (extChartAt I c).symm) (extChartAt I c).target := by
    apply ContMDiffOn.contDiffOn
    exact hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm c)
  have hd := (hf'.differentiableOn
    (by norm_num)).differentiableAt ((isOpen_extChartAt_target (I := I) c).mem_nhds hz)
  change fderiv ℝ (χ * (f ∘ (extChartAt I c).symm)) z v = _
  simpa [Function.comp_def, mul_comm, add_comm] using
    congrArg (fun T : E →L[ℝ] ℝ => T v)
      (fderiv_mul (hχ.differentiable (by simp) z) hd)

/-- The product rule is valid globally because both cutoff terms and the
localized derivative vanish away from the chart target. -/
theorem fderiv_chartCutoff_global (c : M) {χ : E → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hs : tsupport χ ⊆ (extChartAt I c).target)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) (z v : E) :
    fderiv ℝ (chartCutoff (I := I) c χ f) z v =
      fderiv ℝ χ z v * f ((extChartAt I c).symm z) +
        χ z * fderiv ℝ (f ∘ (extChartAt I c).symm) z v := by
  by_cases hz : z ∈ (extChartAt I c).target
  · exact fderiv_chartCutoff c hχ hf hz v
  · have hn : z ∉ tsupport χ := fun h => hz (hs h)
    have hχ0 := image_eq_zero_of_notMem_tsupport hn
    have hdχ : fderiv ℝ χ z = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hn (tsupport_fderiv_subset ℝ h))
    have hd : fderiv ℝ (chartCutoff (I := I) c χ f) z = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun h => hn (tsupport_chartCutoff_subset c χ f (tsupport_fderiv_subset ℝ h)))
    simp [hd, hdχ, hχ0]

end AlmostSchur
