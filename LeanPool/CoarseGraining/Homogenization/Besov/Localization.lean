/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.ProjectionCharacterization

/-! # Localization -/

namespace Homogenization

open MeasureTheory.Measure
open scoped ENNReal

/-!
Localization lemmas for the finite-depth cube Besov package.

This first checkpoint records that the local positive-order quantities attached
to a parent cube `Q` only depend on the function on `cubeSet Q`. These
congruence lemmas are the clean API needed before later descendant-localized
and cutoff-localized estimates are added.
-/

theorem cubeAverage_congr_on_cubeSet {d : ℕ} {Q : TriadicCube d} {u v : Vec d → ℝ}
    (h : ∀ x ∈ cubeSet Q, u x = v x) :
    cubeAverage Q u = cubeAverage Q v := by
  unfold cubeAverage
  refine congrArg (fun t : ℝ => (cubeVolume Q)⁻¹ * t) ?_
  apply MeasureTheory.integral_congr_ae
  exact (MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)).2 <|
    Filter.Eventually.of_forall h

theorem cubeLpNorm_congr_on_cubeSet {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞)
    {u v : Vec d → ℝ} (h : ∀ x ∈ cubeSet Q, u x = v x) :
    cubeLpNorm Q p u = cubeLpNorm Q p v := by
  unfold cubeLpNorm
  rw [MeasureTheory.eLpNorm_congr_ae]
  rw [normalizedCubeMeasure, Filter.EventuallyEq]
  exact ae_smul_measure
    ((MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)).2 <|
      Filter.Eventually.of_forall h)
    (ENNReal.ofReal ((cubeVolume Q)⁻¹))

theorem cubeProjection_congr_on_cubeSet {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    {u v : Vec d → ℝ} (h : ∀ x ∈ cubeSet Q, u x = v x) :
    cubeProjection Q j u = cubeProjection Q j v := by
  funext x
  by_cases hx : x ∈ cubeSet Q
  · rcases exists_mem_descendantsAtDepth_of_mem_cubeSet (n := j) hx with ⟨R, hR, hxR⟩
    rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth u hR hxR,
      cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth v hR hxR]
    apply cubeAverage_congr_on_cubeSet
    intro y hy
    exact h y (cubeSet_subset_of_mem_descendantsAtDepth hR hy)
  · rw [cubeProjection_eq_zero_of_not_mem_cubeSet Q j u hx,
      cubeProjection_eq_zero_of_not_mem_cubeSet Q j v hx]

theorem cubeProjection_ae_eq_cubeProjection_depth_zero_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (f : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j) :
    cubeProjection Q j f =ᵐ[normalizedCubeMeasure R] cubeProjection R 0 f := by
  calc
    cubeProjection Q j f =ᵐ[normalizedCubeMeasure R] fun _ => cubeAverage R f := by
      exact cubeProjection_ae_eq_cubeAverage_of_mem_descendantsAtDepth f hR
    _ =ᵐ[normalizedCubeMeasure R] cubeProjection R 0 f := by
      simpa using
        (cubeProjection_ae_eq_cubeAverage_of_mem_descendantsAtDepth
          (Q := R) (R := R) (j := 0) f (by simp)).symm

theorem cubeProjection_memLp_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (p : ℝ≥0∞) (f : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j) :
    MeasureTheory.MemLp (cubeProjection Q j f) p (normalizedCubeMeasure R) := by
  let c : ℝ := cubeAverage R f
  have hconst : MeasureTheory.MemLp (fun _ : Vec d => c) p (normalizedCubeMeasure R) :=
    MeasureTheory.memLp_const c
  have hproj_meas :
      MeasureTheory.AEStronglyMeasurable (cubeProjection Q j f) (normalizedCubeMeasure R) :=
    hconst.1.congr
      (cubeProjection_ae_eq_cubeAverage_of_mem_descendantsAtDepth (Q := Q) (R := R) (j := j) f hR).symm
  refine hconst.congr_norm hproj_meas ?_
  filter_upwards
    [cubeProjection_ae_eq_cubeAverage_of_mem_descendantsAtDepth (Q := Q) (R := R) (j := j) f hR]
      with x hx
  simpa [c] using (congrArg abs hx).symm

theorem cubeProjectionResidual_ae_eq_cubeProjectionResidual_depth_zero_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (u : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j) :
    cubeProjectionResidual Q j u =ᵐ[normalizedCubeMeasure R] cubeProjectionResidual R 0 u := by
  filter_upwards
    [cubeProjection_ae_eq_cubeProjection_depth_zero_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) u hR] with x hx
  simp [cubeProjectionResidual, hx]

theorem cubeLpNorm_cubeProjectionResidual_eq_cubeProjectionResidual_depth_zero_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (p : ℝ≥0∞) (u : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j) :
    cubeLpNorm R p (cubeProjectionResidual Q j u) =
      cubeLpNorm R p (cubeProjectionResidual R 0 u) := by
  unfold cubeLpNorm
  rw [MeasureTheory.eLpNorm_congr_ae
    (cubeProjectionResidual_ae_eq_cubeProjectionResidual_depth_zero_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) u hR)]

theorem cubeProjectionResidual_memLp_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (p : ℝ≥0∞) (u : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j)
    (hu : MeasureTheory.MemLp (cubeFluctuation R u) p (normalizedCubeMeasure R)) :
    MeasureTheory.MemLp (cubeProjectionResidual Q j u) p (normalizedCubeMeasure R) := by
  have hfluct :
      cubeFluctuation R u =ᵐ[normalizedCubeMeasure R] cubeProjectionResidual Q j u :=
    cubeFluctuation_ae_eq_cubeProjectionResidual_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) u hR
  have hres_meas :
      MeasureTheory.AEStronglyMeasurable (cubeProjectionResidual Q j u)
        (normalizedCubeMeasure R) :=
    hu.1.congr hfluct
  refine hu.congr_norm hres_meas ?_
  filter_upwards [hfluct] with x hx
  simpa using congrArg abs hx

theorem abs_cubeAverage_mul_cubeProjectionResidual_le_mul_cubeLpNorm_cubeBesovOscillation_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (p : ℝ≥0∞) (f u : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j)
    (hf : MeasureTheory.MemLp f p (normalizedCubeMeasure R))
    (hu : MeasureTheory.MemLp (cubeFluctuation R u) (ENNReal.conjExponent p)
      (normalizedCubeMeasure R))
    (hp : 1 ≤ p) :
    |cubeAverage R (fun x => f x * cubeProjectionResidual Q j u x)| ≤
      cubeLpNorm R p f * cubeBesovOscillation R (ENNReal.conjExponent p) u := by
  have hfluct :
      cubeFluctuation R u =ᵐ[normalizedCubeMeasure R] cubeProjectionResidual Q j u :=
    cubeFluctuation_ae_eq_cubeProjectionResidual_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) u hR
  have hres_meas :
      MeasureTheory.AEStronglyMeasurable (cubeProjectionResidual Q j u)
        (normalizedCubeMeasure R) :=
    hu.1.congr hfluct
  have hu_res :
      MeasureTheory.MemLp (cubeProjectionResidual Q j u) (ENNReal.conjExponent p)
        (normalizedCubeMeasure R) := by
    refine hu.congr_norm hres_meas ?_
    filter_upwards [hfluct] with x hx
    simpa using congrArg abs hx
  calc
    |cubeAverage R (fun x => f x * cubeProjectionResidual Q j u x)| ≤
        cubeLpNorm R p f * cubeLpNorm R (ENNReal.conjExponent p) (cubeProjectionResidual Q j u) := by
          exact abs_cubeAverage_mul_le_mul_cubeLpNorm_conjExponent
            R p f (cubeProjectionResidual Q j u) hf hu_res hp
    _ = cubeLpNorm R p f * cubeBesovOscillation R (ENNReal.conjExponent p) u := by
          rw [cubeBesovOscillation_eq_cubeLpNorm_cubeProjectionResidual_of_mem_descendantsAtDepth
            (Q := Q) (R := R) (j := j) (p := ENNReal.conjExponent p) u hR]

theorem abs_cubeAverage_mul_cubeProjection_cubeProjectionResidual_le_abs_cubeAverage_mul_cubeBesovOscillation_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (p : ℝ≥0∞) (f u : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j)
    (hu : MeasureTheory.MemLp (cubeFluctuation R u) (ENNReal.conjExponent p)
      (normalizedCubeMeasure R))
    (hp0 : p ≠ 0) (hp : 1 ≤ p) :
    |cubeAverage R (fun x => cubeProjection Q j f x * cubeProjectionResidual Q j u x)| ≤
      ‖cubeAverage R f‖ * cubeBesovOscillation R (ENNReal.conjExponent p) u := by
  have hproj :
      MeasureTheory.MemLp (cubeProjection Q j f) p (normalizedCubeMeasure R) :=
    cubeProjection_memLp_of_mem_descendantsAtDepth (Q := Q) (R := R) (j := j) p f hR
  calc
    |cubeAverage R (fun x => cubeProjection Q j f x * cubeProjectionResidual Q j u x)| ≤
        cubeLpNorm R p (cubeProjection Q j f) * cubeBesovOscillation R (ENNReal.conjExponent p) u := by
          exact
            abs_cubeAverage_mul_cubeProjectionResidual_le_mul_cubeLpNorm_cubeBesovOscillation_of_mem_descendantsAtDepth
              (Q := Q) (R := R) (j := j) (p := p) (f := cubeProjection Q j f) (u := u)
              hR hproj hu hp
    _ = ‖cubeAverage R f‖ * cubeBesovOscillation R (ENNReal.conjExponent p) u := by
          rw [cubeLpNorm_cubeProjection_eq_abs_cubeAverage_of_mem_descendantsAtDepth
            (Q := Q) (R := R) (j := j) (p := p) (f := f) hR hp0]

theorem cubeVolume_eq_of_mem_descendantsAtDepth {d : ℕ} {Q R S : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (hS : S ∈ descendantsAtDepth Q j) :
    cubeVolume R = cubeVolume S := by
  rw [cubeVolume_eq_pow_scale, cubeVolume_eq_pow_scale,
    scale_eq_sub_of_mem_descendantsAtDepth hR,
    scale_eq_sub_of_mem_descendantsAtDepth hS]

theorem cubeVolume_eq_card_mul_cubeVolume_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) :
    cubeVolume Q = ((descendantsAtDepth Q j).card : ℝ) * cubeVolume R := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  have hmeas : ∀ S ∈ D, MeasurableSet (cubeSet S) := by
    intro S _hS
    exact measurableSet_cubeSet S
  have hpair : (D : Set (TriadicCube d)).PairwiseDisjoint cubeSet := by
    simpa [D] using pairwiseDisjoint_descendantsAtDepth Q j
  have hvol :
      MeasureTheory.volume (cubeSet Q) =
        ∑ S ∈ D, MeasureTheory.volume (cubeSet S) := by
    rw [cubeSet_eq_iUnion_descendantsAtDepth Q j]
    exact MeasureTheory.measure_biUnion_finset (μ := MeasureTheory.volume) hpair hmeas
  have hcube_ne_top : ∀ S ∈ D, MeasureTheory.volume (cubeSet S) ≠ ∞ := by
    intro S _hS htop
    have hreal : (MeasureTheory.volume (cubeSet S)).toReal = cubeVolume S :=
      volume_cubeSet_toReal S
    rw [htop] at hreal
    simp at hreal
    exact (cubeVolume_pos S).ne' hreal.symm
  have hvol_real : cubeVolume Q = ∑ S ∈ D, cubeVolume S := by
    have hvol_toReal :
        (MeasureTheory.volume (cubeSet Q)).toReal =
          (∑ S ∈ D, MeasureTheory.volume (cubeSet S)).toReal :=
      congrArg ENNReal.toReal hvol
    rw [volume_cubeSet_toReal] at hvol_toReal
    rw [ENNReal.toReal_sum hcube_ne_top] at hvol_toReal
    simpa [volume_cubeSet_toReal] using hvol_toReal
  have hsumR : ∑ S ∈ D, cubeVolume S = (D.card : ℝ) * cubeVolume R := by
    calc
      ∑ S ∈ D, cubeVolume S = ∑ S ∈ D, cubeVolume R := by
        refine Finset.sum_congr rfl ?_
        intro S hS
        rw [cubeVolume_eq_of_mem_descendantsAtDepth (Q := Q)
          (by simpa [D] using hS) hR]
      _ = (D.card : ℝ) * cubeVolume R := by
        rw [Finset.sum_const, nsmul_eq_mul]
  simpa [D] using hvol_real.trans hsumR

theorem cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (f : Vec d → ℝ)
    (hf : MeasureTheory.IntegrableOn f (cubeSet Q) MeasureTheory.volume) :
    cubeAverage Q f = descendantsAverage Q j (fun R => cubeAverage R f) := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  have hmeas : ∀ R ∈ D, MeasurableSet (cubeSet R) := by
    intro R hR
    exact measurableSet_cubeSet R
  have hpair : (D : Set (TriadicCube d)).PairwiseDisjoint cubeSet := by
    simpa [D] using pairwiseDisjoint_descendantsAtDepth Q j
  have hint : ∀ R ∈ D, MeasureTheory.IntegrableOn f (cubeSet R) MeasureTheory.volume := by
    intro R hR
    exact hf.mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR)
  have hInt :
      ∫ x in cubeSet Q, f x ∂MeasureTheory.volume =
        ∑ R ∈ D, ∫ x in cubeSet R, f x ∂MeasureTheory.volume := by
    rw [cubeSet_eq_iUnion_descendantsAtDepth Q j]
    exact MeasureTheory.integral_biUnion_finset D hmeas hpair hint
  have hvol :
      MeasureTheory.volume (cubeSet Q) =
        ∑ R ∈ D, MeasureTheory.volume (cubeSet R) := by
    rw [cubeSet_eq_iUnion_descendantsAtDepth Q j]
    exact MeasureTheory.measure_biUnion_finset (μ := MeasureTheory.volume) hpair hmeas
  have hcube_ne_top : ∀ R ∈ D, MeasureTheory.volume (cubeSet R) ≠ ∞ := by
    intro R hR htop
    have hreal : (MeasureTheory.volume (cubeSet R)).toReal = cubeVolume R := volume_cubeSet_toReal R
    rw [htop] at hreal
    simp at hreal
    exact (cubeVolume_pos R).ne' hreal.symm
  have hvol_real : cubeVolume Q = ∑ R ∈ D, cubeVolume R := by
    have hvol_toReal :
        (MeasureTheory.volume (cubeSet Q)).toReal =
          (∑ R ∈ D, MeasureTheory.volume (cubeSet R)).toReal :=
      congrArg ENNReal.toReal hvol
    rw [volume_cubeSet_toReal] at hvol_toReal
    rw [ENNReal.toReal_sum hcube_ne_top] at hvol_toReal
    simpa [volume_cubeSet_toReal] using hvol_toReal
  have hcard_ne : ((D.card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (descendantsAtDepth_nonempty Q j)
  have hcoeff : ∀ R ∈ D, (cubeVolume Q)⁻¹ * cubeVolume R = ((D.card : ℝ)⁻¹) := by
    intro R hR
    have hsumR : ∑ S ∈ D, cubeVolume S = (D.card : ℝ) * cubeVolume R := by
      calc
        ∑ S ∈ D, cubeVolume S = ∑ S ∈ D, cubeVolume R := by
          refine Finset.sum_congr rfl ?_
          intro S hS
          rw [cubeVolume_eq_of_mem_descendantsAtDepth (Q := Q) hS hR]
        _ = (D.card : ℝ) * cubeVolume R := by
          rw [Finset.sum_const, nsmul_eq_mul]
    have hvolR : cubeVolume Q = (D.card : ℝ) * cubeVolume R := by
      rw [hvol_real, hsumR]
    have hR_ne : cubeVolume R ≠ 0 := (cubeVolume_pos R).ne'
    rw [hvolR]
    field_simp [hcard_ne, hR_ne]
  calc
    cubeAverage Q f
        = (cubeVolume Q)⁻¹ * ∑ R ∈ D, ∫ x in cubeSet R, f x ∂MeasureTheory.volume := by
            unfold cubeAverage
            rw [hInt]
    _ = (cubeVolume Q)⁻¹ * ∑ R ∈ D, cubeVolume R * cubeAverage R f := by
          refine congrArg (fun t : ℝ => (cubeVolume Q)⁻¹ * t) ?_
          refine Finset.sum_congr rfl ?_
          intro R hR
          unfold cubeAverage
          have hR_ne : cubeVolume R ≠ 0 := (cubeVolume_pos R).ne'
          field_simp [hR_ne]
    _ = ∑ R ∈ D, ((cubeVolume Q)⁻¹ * cubeVolume R) * cubeAverage R f := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro R hR
          ring
    _ = ∑ R ∈ D, ((D.card : ℝ)⁻¹) * cubeAverage R f := by
          refine Finset.sum_congr rfl ?_
          intro R hR
          rw [hcoeff R hR]
    _ = ((D.card : ℝ)⁻¹) * ∑ R ∈ D, cubeAverage R f := by
          rw [Finset.mul_sum]
    _ = descendantsAverage Q j (fun R => cubeAverage R f) := by
          simp [descendantsAverage, D]

theorem cubeBesovPartialSeminorm_congr_on_cubeSet {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ)
    {u v : Vec d → ℝ} (h : ∀ x ∈ cubeSet Q, u x = v x) :
    cubeBesovPartialSeminorm Q s p q N u = cubeBesovPartialSeminorm Q s p q N v := by
  rw [cubeBesovPartialSeminorm_eq_projection_error,
    cubeBesovPartialSeminorm_eq_projection_error]
  refine congrArg (fun t : ℝ => t ^ (1 / q.toReal)) ?_
  refine Finset.sum_congr rfl ?_
  intro j hj
  refine congrArg (fun t : ℝ =>
    (cubeBesovDepthWeight Q s j * t ^ (1 / p.toReal)) ^ q.toReal) ?_
  unfold descendantsAverage
  refine congrArg (fun t : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
  refine Finset.sum_congr rfl ?_
  intro R hR
  congr 1
  apply cubeLpNorm_congr_on_cubeSet (Q := R) (p := p)
  intro x hxR
  have hxQ : x ∈ cubeSet Q := cubeSet_subset_of_mem_descendantsAtDepth hR hxR
  have hproj :
      cubeProjection Q j u x = cubeProjection Q j v x := by
    simpa using congrArg (fun f : Vec d → ℝ => f x)
      (cubeProjection_congr_on_cubeSet (Q := Q) (j := j) h)
  simp [h x hxQ, hproj]

theorem cubeBesovPartialNorm_congr_on_cubeSet {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ)
    {u v : Vec d → ℝ} (h : ∀ x ∈ cubeSet Q, u x = v x) :
    cubeBesovPartialNorm Q s p q N u = cubeBesovPartialNorm Q s p q N v := by
  unfold cubeBesovPartialNorm
  rw [cubeBesovPartialSeminorm_congr_on_cubeSet Q s p q N h,
    cubeAverage_congr_on_cubeSet h]

end Homogenization
