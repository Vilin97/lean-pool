/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Measure.UniformDensity
public import LeanPool.Besicovitch.Measure.CompactExhaustion

/-!
# Compact uniform-density pieces

An almost-everywhere strict lower-density bound can be made uniform on a compact subset,
while losing arbitrarily little Hausdorff measure.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory Topology

namespace LeanPool.Besicovitch

/-- Increasing the scale index only weakens the defining radius restriction. -/
theorem monotone_uniformDensitySet (mu : Measure (EuclideanSpace ℝ (Fin 2)))
    (A : Set (EuclideanSpace ℝ (Fin 2))) (gamma : ℝ) :
    Monotone fun m ↦ uniformDensitySet mu A gamma m := by
  intro m n hmn x hx
  refine ⟨hx.1, fun q hq hq_small ↦ hx.2 q hq ?_⟩
  refine hq_small.trans_le <| one_div_le_one_div_of_le (by positivity) ?_
  exact_mod_cast Nat.add_le_add_right hmn 1

/-- Lowering the density level enlarges a uniform density set. -/
theorem uniformDensitySet_mono_level {mu : Measure (EuclideanSpace ℝ (Fin 2))}
    {A : Set (EuclideanSpace ℝ (Fin 2))} {beta gamma : ℝ}
    {m : ℕ} (hbeta_gamma : beta ≤ gamma) :
    uniformDensitySet mu A gamma m ⊆ uniformDensitySet mu A beta m := by
  intro x hx
  refine ⟨hx.1, fun q hq hq_small ↦ ?_⟩
  apply (ENNReal.ofReal_le_ofReal ?_).trans (hx.2 q hq hq_small)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hbeta_gamma (by norm_num)) hq.le

/-- A point strictly above level `sigma` belongs to the diagonal uniform-density exhaustion. -/
theorem exists_mem_diagonal_uniformDensitySet_of_lt_lowerOneDensity
    {A : Set (EuclideanSpace ℝ (Fin 2))}
    {x : (EuclideanSpace ℝ (Fin 2))} {sigma : ℝ} (hx : x ∈ A) (hsigma : 0 ≤ sigma)
    (hdensity : ENNReal.ofReal sigma < lowerOneDensity A x) :
    ∃ n : ℕ, x ∈ uniformDensitySet (μH[1].restrict A) A
      (sigma + 1 / (n + 1 : ℝ)) n := by
  have hgap : ∃ k : ℕ,
      ENNReal.ofReal (sigma + 1 / (k + 1 : ℝ)) < lowerOneDensity A x := by
    by_cases htop : lowerOneDensity A x = ∞
    · refine ⟨0, ?_⟩
      rw [htop]
      exact ENNReal.ofReal_lt_top
    · have hsigma_real : sigma < (lowerOneDensity A x).toReal := by
        have hreal := (ENNReal.toReal_lt_toReal (by simp) htop).2 hdensity
        simpa [ENNReal.toReal_ofReal hsigma] using hreal
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hsigma_real)
      refine ⟨k, ?_⟩
      apply (ENNReal.toReal_lt_toReal (by simp) htop).1
      rw [ENNReal.toReal_ofReal (by positivity)]
      linarith
  obtain ⟨k, hk⟩ := hgap
  have hlevel_nonneg : 0 ≤ sigma + 1 / (k + 1 : ℝ) := by positivity
  obtain ⟨m, hm⟩ :=
    exists_mem_uniformDensitySet_of_lt_lowerOneDensity hx hlevel_nonneg hk
  let n := max k m
  refine ⟨n, ?_⟩
  apply monotone_uniformDensitySet _ _ _ (le_max_right k m)
  apply uniformDensitySet_mono_level ?_ hm
  have hone : 1 / (n + 1 : ℝ) ≤ 1 / (k + 1 : ℝ) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right (le_max_left k m) 1
  linarith

/-- Almost every point lies in a uniform-density set when its lower density exceeds the level. -/
theorem ae_mem_iUnion_uniformDensitySet
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : MeasurableSet A)
    {gamma : ℝ} (hgamma : 0 ≤ gamma)
    (hdensity : ∀ᵐ x ∂μH[1].restrict A,
      ENNReal.ofReal gamma < lowerOneDensity A x) :
    ∀ᵐ x ∂μH[1].restrict A, x ∈ ⋃ m, uniformDensitySet (μH[1].restrict A) A gamma m := by
  filter_upwards [ae_restrict_mem hA, hdensity] with x hxA hxDensity
  obtain ⟨m, hm⟩ :=
    exists_mem_uniformDensitySet_of_lt_lowerOneDensity hxA hgamma hxDensity
  exact mem_iUnion.2 ⟨m, hm⟩

/-- Almost-everywhere density gives an arbitrarily small exceptional set at one uniform scale. -/
theorem exists_uniformDensitySet_measure_sdiff_lt
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : MeasurableSet A)
    {gamma : ℝ} (hgamma : 0 ≤ gamma)
    (hdensity : ∀ᵐ x ∂μH[1].restrict A,
      ENNReal.ofReal gamma < lowerOneDensity A x)
    (hfinite : μH[1] A ≠ ∞)
    {epsilon : ℝ≥0∞} (hepsilon : 0 < epsilon) :
    ∃ m : ℕ, μH[1] (A \ uniformDensitySet (μH[1].restrict A) A gamma m) < epsilon := by
  let : IsFiniteMeasure (μH[1].restrict A) := isFiniteMeasure_restrict.mpr hfinite
  exact exists_in_monotone_ae_cover_measure_sdiff_lt hA hfinite
    (fun _ ↦ measurableSet_uniformDensitySet _ hA _ _)
    (monotone_uniformDensitySet _ _ _)
    (ae_mem_iUnion_uniformDensitySet hA hgamma hdensity) hepsilon

/-- A compact uniform-density piece can retain all but any prescribed positive mass. -/
theorem exists_compact_uniformDensitySet_measure_sdiff_lt {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : MeasurableSet A) {gamma : ℝ} (hgamma : 0 ≤ gamma)
    (hdensity : ∀ᵐ x ∂μH[1].restrict A,
      ENNReal.ofReal gamma < lowerOneDensity A x)
    (hfinite : μH[1] A ≠ ∞) {epsilon : ℝ≥0∞} (hepsilon : 0 < epsilon) :
    ∃ (m : ℕ) (F : Set (EuclideanSpace ℝ (Fin 2))), IsCompact F ∧
      F ⊆ uniformDensitySet (μH[1].restrict A) A gamma m ∧ μH[1] (A \ F) < epsilon := by
  let : IsFiniteMeasure (μH[1].restrict A) := isFiniteMeasure_restrict.mpr hfinite
  exact exists_compact_in_monotone_ae_cover_measure_sdiff_lt hA hfinite
    (fun _ ↦ measurableSet_uniformDensitySet _ hA _ _)
    (fun _ _ hx ↦ hx.1) (monotone_uniformDensitySet _ _ _)
    (ae_mem_iUnion_uniformDensitySet hA hgamma hdensity) hepsilon

/-- The compact core can be chosen so that the discarded mass is a prescribed fraction of it. -/
theorem exists_compact_uniformDensitySet_measure_sdiff_lt_mul {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : MeasurableSet A) (hA_pos : 0 < μH[1] A) (hA_finite : μH[1] A ≠ ∞)
    {gamma alpha : ℝ} (hgamma : 0 ≤ gamma) (halpha : 0 < alpha)
    (hdensity : ∀ᵐ x ∂μH[1].restrict A,
      ENNReal.ofReal gamma < lowerOneDensity A x) :
    ∃ (m : ℕ) (F : Set (EuclideanSpace ℝ (Fin 2))), IsCompact F ∧
      F ⊆ uniformDensitySet (μH[1].restrict A) A gamma m ∧
        μH[1] (A \ F) < ENNReal.ofReal alpha * μH[1] F := by
  let : IsFiniteMeasure (μH[1].restrict A) := isFiniteMeasure_restrict.mpr hA_finite
  exact exists_compact_in_monotone_ae_cover_measure_sdiff_lt_mul hA hA_pos hA_finite
    (fun _ ↦ measurableSet_uniformDensitySet _ hA _ _)
    (fun _ _ hx ↦ hx.1) (monotone_uniformDensitySet _ _ _)
    (ae_mem_iUnion_uniformDensitySet hA hgamma hdensity)
    (ENNReal.ofReal_pos.2 halpha) ENNReal.ofReal_ne_top

/-- An almost-everywhere density bound strictly above `sigma` is uniform at a common higher level
on a compact core whose discarded mass is a prescribed fraction of the retained mass. -/
theorem exists_compact_uniformDensitySet_above
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : MeasurableSet A)
    (hA_pos : 0 < μH[1] A) (hA_finite : μH[1] A ≠ ∞) {sigma alpha : ℝ}
    (hsigma : 0 ≤ sigma) (halpha : 0 < alpha)
    (hdensity : ∀ᵐ x ∂μH[1].restrict A,
      ENNReal.ofReal sigma < lowerOneDensity A x) :
    ∃ (gamma : ℝ) (m : ℕ) (F : Set (EuclideanSpace ℝ (Fin 2))),
      sigma < gamma ∧ IsCompact F ∧
      F ⊆ uniformDensitySet (μH[1].restrict A) A gamma m ∧
        μH[1] (A \ F) < ENNReal.ofReal alpha * μH[1] F := by
  let : IsFiniteMeasure (μH[1].restrict A) := isFiniteMeasure_restrict.mpr hA_finite
  let G : ℕ → Set (EuclideanSpace ℝ (Fin 2)) := fun n ↦
    uniformDensitySet (μH[1].restrict A) A (sigma + 1 / (n + 1 : ℝ)) n
  have hG_measurable (n : ℕ) : MeasurableSet (G n) :=
    measurableSet_uniformDensitySet _ hA _ _
  have hG_subset (n : ℕ) : G n ⊆ A := fun _ hx ↦ hx.1
  have hG_mono : Monotone G := by
    intro m n hmn x hx
    apply monotone_uniformDensitySet _ _ _ hmn
    apply uniformDensitySet_mono_level ?_ hx
    have hone : 1 / (n + 1 : ℝ) ≤ 1 / (m + 1 : ℝ) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hmn 1
    linarith
  have hcovered : ∀ᵐ x ∂μH[1].restrict A, x ∈ ⋃ n, G n := by
    filter_upwards [ae_restrict_mem hA, hdensity] with x hxA hxDensity
    obtain ⟨n, hn⟩ :=
      exists_mem_diagonal_uniformDensitySet_of_lt_lowerOneDensity hxA hsigma hxDensity
    exact mem_iUnion.2 ⟨n, hn⟩
  obtain ⟨n, F, hF_compact, hFG, herror⟩ :=
    exists_compact_in_monotone_ae_cover_measure_sdiff_lt_mul hA hA_pos hA_finite
      hG_measurable hG_subset hG_mono hcovered (ENNReal.ofReal_pos.2 halpha)
      ENNReal.ofReal_ne_top
  refine ⟨sigma + 1 / (n + 1 : ℝ), n, F, ?_, hF_compact, ?_, herror⟩
  · have : 0 < 1 / (n + 1 : ℝ) := by positivity
    linarith
  exact hFG

end LeanPool.Besicovitch
