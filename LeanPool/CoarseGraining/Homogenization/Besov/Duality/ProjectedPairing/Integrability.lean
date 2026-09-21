/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Duality.ProjectedPairing.Projections

/-! # Integrability -/

namespace Homogenization

open MeasureTheory.Measure
open scoped BigOperators ENNReal
theorem integrableOn_of_integrable_normalizedCubeMeasure {d : ℕ} (Q : TriadicCube d)
    {f : Vec d → ℝ}
    (hf : MeasureTheory.Integrable f (normalizedCubeMeasure Q)) :
    MeasureTheory.IntegrableOn f (cubeSet Q) MeasureTheory.volume := by
  have hscale_ne_zero : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 := by
    have hscale_pos : 0 < ENNReal.ofReal ((cubeVolume Q)⁻¹) := by
      exact ENNReal.ofReal_pos.mpr (inv_pos.mpr (cubeVolume_pos Q))
    exact hscale_pos.ne'
  change MeasureTheory.Integrable f (MeasureTheory.volume.restrict (cubeSet Q)) at ⊢
  rw [normalizedCubeMeasure, cubeMeasure] at hf
  exact (MeasureTheory.integrable_smul_measure
    (μ := MeasureTheory.volume.restrict (cubeSet Q)) hscale_ne_zero ENNReal.ofReal_ne_top).1
    hf

theorem integrableOn_mul_projectionResidual_projection_succ_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (p : ℝ≥0∞) (f g : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j)
    (hf : MeasureTheory.MemLp (cubeFluctuation R f) p (normalizedCubeMeasure R))
    (hg : MeasureTheory.MemLp (cubeProjection Q (j + 1) g)
      (cubeBesovConjExponent p) (normalizedCubeMeasure R))
    (hp : 1 ≤ p) :
    MeasureTheory.IntegrableOn
      (fun x => cubeProjection Q (j + 1) g x * cubeProjectionResidual Q j f x)
      (cubeSet R) MeasureTheory.volume := by
  let q : ℝ≥0∞ := cubeBesovConjExponent p
  let : ENNReal.HolderConjugate p q :=
    by simpa [q, cubeBesovConjExponent] using ENNReal.HolderConjugate.conjExponent hp
  have hres :
      MeasureTheory.MemLp (cubeProjectionResidual Q j f) p (normalizedCubeMeasure R) :=
    cubeProjectionResidual_memLp_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) (p := p) (u := f) hR hf
  have hint :
      MeasureTheory.Integrable
        (fun x => cubeProjection Q (j + 1) g x * cubeProjectionResidual Q j f x)
        (normalizedCubeMeasure R) := by
    simpa [q] using! hg.integrable_mul hres
  exact integrableOn_of_integrable_normalizedCubeMeasure (Q := R) hint

theorem integrableOn_mul_projection_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (p : ℝ≥0∞) (f g : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j)
    (hf : MeasureTheory.MemLp (cubeFluctuation R f) p (normalizedCubeMeasure R))
    (hp : 1 ≤ p) :
    MeasureTheory.IntegrableOn
      (fun x => f x * cubeProjection Q j g x)
      (cubeSet R) MeasureTheory.volume := by
  let q : ℝ≥0∞ := cubeBesovConjExponent p
  let : ENNReal.HolderConjugate p q :=
    by simpa [q, cubeBesovConjExponent] using ENNReal.HolderConjugate.conjExponent hp
  have hres :
      MeasureTheory.MemLp (cubeProjectionResidual Q j f) p (normalizedCubeMeasure R) :=
    cubeProjectionResidual_memLp_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) (p := p) (u := f) hR hf
  have hprojf :
      MeasureTheory.MemLp (cubeProjection Q j f) p (normalizedCubeMeasure R) :=
    cubeProjection_memLp_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) (p := p) (f := f) hR
  have hprojg :
      MeasureTheory.MemLp (cubeProjection Q j g) q (normalizedCubeMeasure R) :=
    cubeProjection_memLp_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) (p := q) (f := g) hR
  have hfirst_int :
      MeasureTheory.Integrable
        (fun x => cubeProjection Q j f x * cubeProjection Q j g x)
        (normalizedCubeMeasure R) := by
    simpa [q, mul_comm] using! hprojg.integrable_mul hprojf
  have hsecond_int_raw :
      MeasureTheory.Integrable
        (fun x => cubeProjection Q j g x * cubeProjectionResidual Q j f x)
        (normalizedCubeMeasure R) := by
    simpa [q] using! hprojg.integrable_mul hres
  have hsecond_int :
      MeasureTheory.Integrable
        (fun x => cubeProjectionResidual Q j f x * cubeProjection Q j g x)
        (normalizedCubeMeasure R) := by
    refine hsecond_int_raw.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    simp [mul_comm]
  have hsum_int :
      MeasureTheory.Integrable
        (fun x =>
          cubeProjection Q j f x * cubeProjection Q j g x +
            cubeProjectionResidual Q j f x * cubeProjection Q j g x)
        (normalizedCubeMeasure R) :=
    hfirst_int.add hsecond_int
  refine integrableOn_of_integrable_normalizedCubeMeasure (Q := R) ?_
  refine hsum_int.congr ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  symm
  calc
    f x * cubeProjection Q j g x
        = (cubeProjection Q j f x + cubeProjectionResidual Q j f x) *
            cubeProjection Q j g x := by
              simp [cubeProjectionResidual]
    _ = cubeProjection Q j f x * cubeProjection Q j g x +
          cubeProjectionResidual Q j f x * cubeProjection Q j g x := by
            rw [add_mul]

theorem integrableOn_mul_projection_succ_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (p : ℝ≥0∞) (f g : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j)
    (hf : MeasureTheory.MemLp (cubeFluctuation R f) p (normalizedCubeMeasure R))
    (hg : MeasureTheory.MemLp (cubeProjection Q (j + 1) g)
      (cubeBesovConjExponent p) (normalizedCubeMeasure R))
    (hp : 1 ≤ p) :
    MeasureTheory.IntegrableOn
      (fun x => f x * cubeProjection Q (j + 1) g x)
      (cubeSet R) MeasureTheory.volume := by
  let q : ℝ≥0∞ := cubeBesovConjExponent p
  let : ENNReal.HolderConjugate p q :=
    by simpa [q, cubeBesovConjExponent] using ENNReal.HolderConjugate.conjExponent hp
  have hres :
      MeasureTheory.MemLp (cubeProjectionResidual Q j f) p (normalizedCubeMeasure R) :=
    cubeProjectionResidual_memLp_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) (p := p) (u := f) hR hf
  have hprojf :
      MeasureTheory.MemLp (cubeProjection Q j f) p (normalizedCubeMeasure R) :=
    cubeProjection_memLp_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) (p := p) (f := f) hR
  have hfirst_int :
      MeasureTheory.Integrable
        (fun x => cubeProjection Q j f x * cubeProjection Q (j + 1) g x)
        (normalizedCubeMeasure R) := by
    simpa [q, mul_comm] using! hg.integrable_mul hprojf
  have hsecond_int_raw :
      MeasureTheory.Integrable
        (fun x => cubeProjection Q (j + 1) g x * cubeProjectionResidual Q j f x)
        (normalizedCubeMeasure R) := by
    simpa [q] using! hg.integrable_mul hres
  have hsecond_int :
      MeasureTheory.Integrable
        (fun x => cubeProjectionResidual Q j f x * cubeProjection Q (j + 1) g x)
        (normalizedCubeMeasure R) := by
    refine hsecond_int_raw.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    simp [mul_comm]
  have hsum_int :
      MeasureTheory.Integrable
        (fun x =>
          cubeProjection Q j f x * cubeProjection Q (j + 1) g x +
            cubeProjectionResidual Q j f x * cubeProjection Q (j + 1) g x)
        (normalizedCubeMeasure R) :=
    hfirst_int.add hsecond_int
  refine integrableOn_of_integrable_normalizedCubeMeasure (Q := R) ?_
  refine hsum_int.congr ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  symm
  calc
    f x * cubeProjection Q (j + 1) g x
        = (cubeProjection Q j f x + cubeProjectionResidual Q j f x) *
            cubeProjection Q (j + 1) g x := by
              simp [cubeProjectionResidual]
    _ = cubeProjection Q j f x * cubeProjection Q (j + 1) g x +
          cubeProjectionResidual Q j f x * cubeProjection Q (j + 1) g x := by
            rw [add_mul]

theorem cubeAverage_cubeProjectionResidual_depth_zero_eq_zero_of_memLp {d : ℕ}
    (Q : TriadicCube d) (p : ℝ≥0∞) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp (cubeProjectionResidual Q 0 f) p (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) :
    cubeAverage Q (cubeProjectionResidual Q 0 f) = 0 := by
  have hres_int :
      MeasureTheory.Integrable (cubeProjectionResidual Q 0 f) (normalizedCubeMeasure Q) :=
    hf.integrable hp
  have hproj_int :
      MeasureTheory.Integrable (cubeProjection Q 0 f) (normalizedCubeMeasure Q) := by
    exact
      (cubeProjection_memLp_of_mem_descendantsAtDepth
        (Q := Q) (R := Q) (j := 0) (p := (1 : ℝ≥0∞)) (f := f) (by simp)).integrable
        (by norm_num)
  have hf_int : MeasureTheory.Integrable f (normalizedCubeMeasure Q) := by
    refine (hres_int.add hproj_int).congr ?_
    filter_upwards with x
    simp [cubeProjectionResidual]
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  change ∫ x, (f x - cubeProjection Q 0 f x) ∂ normalizedCubeMeasure Q = 0
  rw [MeasureTheory.integral_sub hf_int hproj_int]
  have hproj_avg :
      ∫ x, cubeProjection Q 0 f x ∂ normalizedCubeMeasure Q = cubeAverage Q f := by
    calc
      ∫ x, cubeProjection Q 0 f x ∂ normalizedCubeMeasure Q
          = ∫ x, cubeAverage Q f ∂ normalizedCubeMeasure Q := by
              refine MeasureTheory.integral_congr_ae ?_
              simpa using
                cubeProjection_ae_eq_cubeAverage_of_mem_descendantsAtDepth
                  (Q := Q) (R := Q) (j := 0) f (by simp)
      _ = cubeAverage Q f := by
            rw [MeasureTheory.integral_const]
            simp [MeasureTheory.measureReal_def]
  rw [hproj_avg, cubeAverage_eq_integral_normalizedCubeMeasure]
  ring

end Homogenization
