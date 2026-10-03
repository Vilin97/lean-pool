/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integration in polar coordinates (ported from TauCeti)

Let `E` be a nontrivial finite-dimensional real normed space of dimension `n` with an additive
Haar measure `μ`. Mathlib's `MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd`
identifies `μ` on `E \ {0}` with the product of the surface measure `μ.toSphere` on the unit
sphere and the radial measure `r ^ (n - 1) dr` on `(0, ∞)`, but upstream only integrates radial
functions against it (`MeasureTheory.integral_fun_norm_addHaar`). This file records the
integral formula for an arbitrary integrable function, in both orders of integration,

`∫ x, f x ∂μ = ∫ u ∈ S, ∫ r in (0, ∞), r ^ (n - 1) • f (r • u) ∂μ.toSphere`
` = ∫ r in (0, ∞), r ^ (n - 1) • ∫ u ∈ S, f (r • u) ∂μ.toSphere`.

## Main declarations

* `integral_volumeIoiPow`: integration against `Measure.volumeIoiPow k` is integration on
  `(0, ∞)` against the weight `r ^ k`.
* `integral_eq_integral_toSphere_integral_Ioi`, `integral_eq_integral_Ioi_integral_toSphere`:
  integration in polar coordinates.
* `continuousOn_integral_toSphere_smul`: the sphere integrals `r ↦ ∫ u ∈ S, f (r • u)` depend
  continuously on `r ∈ [0, R]` when `f` is continuous on the closed ball of radius `R`.

## Provenance

Pool port: imports relocated under `LeanPool.ViscositySolutionTheory`; original
mathematical namespaces and copyright retained; checked with Lean/Mathlib v4.34.0.


* Upstream: TauCeti, https://github.com/TauCetiProject/TauCeti
* Path: `TauCeti/MeasureTheory/Constructions/HaarToSphere.lean`
* Commit: 91f66a0514e6523efdccddb9e35fb82c96dd6405 (2026-09-24)
* License: Apache-2.0. Upstream `NOTICE`: none.
* Upstream notice: `Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.`;
  upstream authors: The Tau Ceti contributors.
* Extent: `integral_volumeIoiPow`, `integrable_and_integral_eq_integral_prod_toSphere`,
  `integral_eq_integral_toSphere_integral_Ioi`, `integral_eq_integral_Ioi_integral_toSphere`,
  `ContinuousOn.integral_toSphere_smul` (verbatim up to naming).
* Changes: ported from Lean v4.34.0-rc2 to Lean/Mathlib v4.30.0; `module`/`public import`
  removed; namespace `TauCeti` → `ViscositySolns.Analysis`; `ContinuousOn.integral_toSphere_smul`
  renamed `continuousOn_integral_toSphere_smul`; the radial fundamental theorem of calculus
  (`integral_norm_rpow_neg_finrank_mul_fderiv_apply_self`) is not ported.
-/

@[expose] public noncomputable section

namespace ViscositySolns

namespace Analysis

open MeasureTheory Metric Set Filter Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Integration against `MeasureTheory.Measure.volumeIoiPow k` is integration on `(0, ∞)`
against the weight `r ^ k`. -/
theorem integral_volumeIoiPow (k : ℕ) (h : ℝ → F) :
    ∫ r : Ioi (0 : ℝ), h r ∂(Measure.volumeIoiPow k) = ∫ r in Ioi (0 : ℝ), r ^ k • h r := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul (measurable_subtype_coe.pow_const _).real_toNNReal,
    integral_subtype_comap measurableSet_Ioi fun r ↦ Real.toNNReal (r ^ k) • h r]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
  rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg (le_of_lt hr) _)]

/-- The polar-coordinate identification of `μ` with the product of `μ.toSphere` and the radial
measure, for an integrable function: the transported integrand is integrable for the product
measure, and integrates to `∫ f ∂μ`. -/
private lemma integrable_and_integral_eq_integral_prod_toSphere (f : E → F)
    (hf : Integrable f μ) :
    Integrable (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) ↦ f ((p.2 : ℝ) • (p.1 : E)))
        (μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) ∧
      ∫ x, f x ∂μ = ∫ p : sphere (0 : E) 1 × Ioi (0 : ℝ), f ((p.2 : ℝ) • (p.1 : E))
        ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
  set k := Module.finrank ℝ E - 1
  have hmp := μ.measurePreserving_homeomorphUnitSphereProd
  have hemb := (homeomorphUnitSphereProd E).measurableEmbedding
  set g : sphere (0 : E) 1 × Ioi (0 : ℝ) → F := fun p ↦ f ((p.2 : ℝ) • (p.1 : E)) with hg_def
  have hg : g ∘ homeomorphUnitSphereProd E = f ∘ Subtype.val := by
    funext x
    have hx : ‖(x : E)‖ ≠ 0 := norm_ne_zero_iff.mpr x.2
    simp [hg_def, smul_smul, hx]
  refine ⟨?_, ?_⟩
  · rw [← hmp.integrable_comp_emb hemb, hg,
      ← integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl]
    exact hf.integrableOn
  calc ∫ x, f x ∂μ = ∫ x : ({0}ᶜ : Set E), f x ∂(μ.comap Subtype.val) := by
        rw [integral_subtype_comap (measurableSet_singleton _).compl f,
          restrict_compl_singleton]
    _ = ∫ p, g p ∂(μ.toSphere.prod (Measure.volumeIoiPow k)) := by
        rw [← hmp.integral_comp hemb g]
        exact integral_congr_ae (ae_of_all _ fun x ↦ (congrFun hg x).symm)

/-- **Integration in polar coordinates.** An integrable function on a finite-dimensional real
normed space is integrated by first integrating along each ray `r ↦ r • u`, against the radial
Jacobian `r ^ (d - 1)`, and then over the unit sphere against `μ.toSphere`. -/
theorem integral_eq_integral_toSphere_integral_Ioi (f : E → F) (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∫ u : sphere (0 : E) 1, (∫ r in Ioi (0 : ℝ),
      r ^ (Module.finrank ℝ E - 1) • f (r • (u : E))) ∂μ.toSphere := by
  obtain ⟨hint, heq⟩ := integrable_and_integral_eq_integral_prod_toSphere f hf
  rw [heq, integral_prod _ hint]
  exact integral_congr_ae (ae_of_all _ fun u ↦
    integral_volumeIoiPow (Module.finrank ℝ E - 1) fun r ↦ f (r • (u : E)))

/-- **Integration in polar coordinates, radial variable outermost.** An integrable function on a
finite-dimensional real normed space is integrated by first integrating over the sphere of radius
`r` (parametrized by the unit sphere against `μ.toSphere`), and then in `r` against the radial
Jacobian `r ^ (d - 1)`. -/
theorem integral_eq_integral_Ioi_integral_toSphere (f : E → F) (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∫ r in Ioi (0 : ℝ), r ^ (Module.finrank ℝ E - 1) •
      ∫ u : sphere (0 : E) 1, f (r • (u : E)) ∂μ.toSphere := by
  obtain ⟨hint, heq⟩ := integrable_and_integral_eq_integral_prod_toSphere f hf
  rw [heq, integral_prod_symm _ hint]
  exact integral_volumeIoiPow (Module.finrank ℝ E - 1)
    fun r ↦ ∫ u : sphere (0 : E) 1, f (r • (u : E)) ∂μ.toSphere

omit [Nontrivial E] in
/-- The integral of `f` over the sphere of radius `r` about the origin, parametrized by the unit
sphere, depends continuously on `r ∈ [0, R]` when `f` is continuous on the closed ball of radius
`R`. -/
theorem continuousOn_integral_toSphere_smul {f : E → F} {R : ℝ}
    (hf : ContinuousOn f (closedBall (0 : E) R)) :
    ContinuousOn (fun r : ℝ ↦ ∫ u : sphere (0 : E) 1, f (r • (u : E)) ∂μ.toSphere) (Icc 0 R) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hf
  have hmem : ∀ r ∈ Icc (0 : ℝ) R, ∀ u : sphere (0 : E) 1,
      r • (u : E) ∈ closedBall (0 : E) R := by
    intro r hr u
    rw [mem_closedBall_zero_iff, norm_smul, norm_eq_of_mem_sphere u, mul_one,
      Real.norm_of_nonneg hr.1]
    exact hr.2
  refine continuousOn_of_dominated (bound := fun _ ↦ C) (fun r hr ↦ ?_) (fun r hr ↦ ?_)
    (integrable_const C) (ae_of_all _ fun u ↦ ?_)
  · exact (hf.comp_continuous (continuous_const.smul continuous_subtype_val)
      (hmem r hr)).aestronglyMeasurable
  · exact ae_of_all _ fun u ↦ hC _ (hmem r hr u)
  · exact hf.comp (continuous_id.smul continuous_const).continuousOn fun r hr ↦ hmem r hr u

end Analysis

end ViscositySolns
