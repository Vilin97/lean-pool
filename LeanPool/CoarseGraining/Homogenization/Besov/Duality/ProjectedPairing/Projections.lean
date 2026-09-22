/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Duality.Definitions

/-! # Projections -/

namespace Homogenization

open MeasureTheory.Measure
open scoped BigOperators ENNReal

theorem cubeProjection_one_memLp {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞)
    (g : Vec d → ℝ) :
    MeasureTheory.MemLp (cubeProjection Q 1 g) p (normalizedCubeMeasure Q) := by
  classical
  unfold cubeProjection
  rw [descendantsAtDepth_one]
  refine MeasureTheory.memLp_finsetSum
    (s := childCubes Q)
    (f := fun R : TriadicCube d => fun x : Vec d =>
      if x ∈ cubeSet R then cubeAverage R g else 0) ?_
  intro R hR
  have hR_ne_top : normalizedCubeMeasure Q (cubeSet R) ≠ ∞ := by
    have hR_le : normalizedCubeMeasure Q (cubeSet R) ≤ normalizedCubeMeasure Q Set.univ :=
      MeasureTheory.measure_mono (Set.subset_univ (cubeSet R))
    have hUniv_lt : normalizedCubeMeasure Q Set.univ < ∞ := by simp
    exact ne_of_lt (lt_of_le_of_lt hR_le hUniv_lt)
  simpa [Set.indicator] using!
    (MeasureTheory.memLp_indicator_const (μ := normalizedCubeMeasure Q)
      (p := p) (s := cubeSet R) (hs := measurableSet_cubeSet R)
      (c := cubeAverage R g) (Or.inr hR_ne_top))

theorem cubeProjection_succ_ae_eq_cubeProjection_one_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (g : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j) :
    cubeProjection Q (j + 1) g =ᵐ[normalizedCubeMeasure R] cubeProjection R 1 g := by
  rw [normalizedCubeMeasure, Filter.EventuallyEq]
  exact ae_smul_measure
    ((MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet R)).2 <|
      Filter.Eventually.of_forall fun x hx => by
        rcases exists_mem_descendantsAtDepth_of_mem_cubeSet (Q := R) (n := 1) hx with
          ⟨S, hS, hxS⟩
        have hSQ : S ∈ descendantsAtDepth Q (j + 1) := by
          exact (mem_descendantsAtDepth_succ_iff).2
            ⟨R, hR, by simpa [descendantsAtDepth_one] using hS⟩
        rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
              (Q := Q) (R := S) (j := j + 1) g hSQ hxS,
            cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
              (Q := R) (R := S) (j := 1) g hS hxS])
    (ENNReal.ofReal ((cubeVolume R)⁻¹))

theorem cubeProjection_succ_memLp_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (p : ℝ≥0∞) (g : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j) :
    MeasureTheory.MemLp (cubeProjection Q (j + 1) g) p (normalizedCubeMeasure R) := by
  have hone : MeasureTheory.MemLp (cubeProjection R 1 g) p (normalizedCubeMeasure R) :=
    cubeProjection_one_memLp R p g
  have hEq :
      cubeProjection Q (j + 1) g =ᵐ[normalizedCubeMeasure R] cubeProjection R 1 g :=
    cubeProjection_succ_ae_eq_cubeProjection_one_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) g hR
  have hproj_meas :
      MeasureTheory.AEStronglyMeasurable (cubeProjection Q (j + 1) g)
        (normalizedCubeMeasure R) :=
    hone.aestronglyMeasurable.congr hEq.symm
  refine hone.congr_norm hproj_meas ?_
  filter_upwards [hEq] with x hx
  simpa using congrArg abs hx.symm

theorem descendantsAverage_cubeLpNorm_projection_succ_eq_cubeBesovCircDepthAverage {d : ℕ}
    (Q : TriadicCube d) (p : ℝ≥0∞) (g : Vec d → ℝ) (j : ℕ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (hg : ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp (cubeProjection Q (j + 1) g) p (normalizedCubeMeasure R)) :
    descendantsAverage Q j (fun R =>
      (cubeLpNorm R p (cubeProjection Q (j + 1) g)) ^ p.toReal) =
      cubeBesovCircDepthAverage Q p g (j + 1) := by
  classical
  have hlocal :
      ∀ R ∈ descendantsAtDepth Q j,
        (cubeLpNorm R p (cubeProjection Q (j + 1) g)) ^ p.toReal =
          descendantsAverage R 1 (fun S => ‖cubeAverage S g‖ ^ p.toReal) := by
    intro R hR
    have hnorm_int_norm :
        MeasureTheory.Integrable (fun x => ‖cubeProjection Q (j + 1) g x‖ ^ p.toReal)
          (normalizedCubeMeasure R) :=
      (hg R hR).integrable_norm_rpow hp0 hpTop
    have hscale_ne_zero : ENNReal.ofReal ((cubeVolume R)⁻¹) ≠ 0 := by
      have hscale_pos : 0 < ENNReal.ofReal ((cubeVolume R)⁻¹) := by
        exact ENNReal.ofReal_pos.mpr (inv_pos.mpr (cubeVolume_pos R))
      exact hscale_pos.ne'
    have hnorm_int :
        MeasureTheory.IntegrableOn (fun x => ‖cubeProjection Q (j + 1) g x‖ ^ p.toReal)
          (cubeSet R) MeasureTheory.volume := by
      unfold MeasureTheory.IntegrableOn at hnorm_int_norm ⊢
      rw [normalizedCubeMeasure, cubeMeasure] at hnorm_int_norm
      exact (MeasureTheory.integrable_smul_measure
        (μ := MeasureTheory.volume.restrict (cubeSet R)) hscale_ne_zero ENNReal.ofReal_ne_top).1
        hnorm_int_norm
    rw [cubeLpNorm_rpow_eq_cubeAverage_norm_rpow (Q := R) (p := p)
      (f := cubeProjection Q (j + 1) g) hp0 hpTop (hg R hR)]
    rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
      (Q := R) (j := 1) (f := fun x => ‖cubeProjection Q (j + 1) g x‖ ^ p.toReal) hnorm_int]
    unfold descendantsAverage
    refine congrArg (fun t : ℝ => ((descendantsAtDepth R 1).card : ℝ)⁻¹ * t) ?_
    refine Finset.sum_congr rfl ?_
    intro S hS
    have hcongr :
        cubeAverage S (fun x => ‖cubeProjection Q (j + 1) g x‖ ^ p.toReal) =
          cubeAverage S (fun _ => ‖cubeAverage S g‖ ^ p.toReal) := by
      apply (cubeAverage_congr_on_cubeSet (Q := S))
      intro x hxS
      have hSQ : S ∈ descendantsAtDepth Q (j + 1) := by
        rw [descendantsAtDepth_succ]
        exact Finset.mem_biUnion.mpr ⟨R, hR, by simpa [descendantsAtDepth_one] using hS⟩
      rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
        (Q := Q) (R := S) (j := j + 1) g hSQ hxS]
    rw [hcongr, cubeAverage_const]
  calc
    descendantsAverage Q j (fun R =>
      (cubeLpNorm R p (cubeProjection Q (j + 1) g)) ^ p.toReal)
        = descendantsAverage Q j (fun R =>
            descendantsAverage R 1 (fun S => ‖cubeAverage S g‖ ^ p.toReal)) := by
              unfold descendantsAverage
              refine congrArg (fun t : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
              refine Finset.sum_congr rfl ?_
              intro R hR
              rw [hlocal R hR]
              rfl
    _ = descendantsAverage Q (j + 1) (fun S => ‖cubeAverage S g‖ ^ p.toReal) := by
          rw [descendantsAverage_succ_eq_descendantsAverage_descendantsAverage]
    _ = cubeBesovCircDepthAverage Q p g (j + 1) := by
          rfl

theorem abs_cubeAverage_mul_projection_succ_projectionResidual_le_mul_cubeBesovCircDepthAverage
    {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞) (f g : Vec d → ℝ) (j : ℕ)
    (hp : 1 ≤ p) (_hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hf : ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp (cubeFluctuation R f) p (normalizedCubeMeasure R))
    (hg : ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp (cubeProjection Q (j + 1) g)
        (cubeBesovConjExponent p) (normalizedCubeMeasure R)) :
    |cubeAverage Q (fun x => cubeProjection Q (j + 1) g x * cubeProjectionResidual Q j f x)| ≤
      (cubeBesovCircDepthAverage Q (cubeBesovConjExponent p) g (j + 1)) ^
        (1 / (cubeBesovConjExponent p).toReal) *
      (cubeBesovDepthAverage Q p f j) ^ (1 / p.toReal) := by
  classical
  let q : ℝ≥0∞ := cubeBesovConjExponent p
  let : ENNReal.HolderConjugate p q :=
    by simpa [q, cubeBesovConjExponent] using ENNReal.HolderConjugate.conjExponent hp
  let : ENNReal.HolderConjugate q p := inferInstance
  have hq : 1 ≤ q := ENNReal.HolderConjugate.one_le (p := q) (q := p)
  have hqTop : q ≠ ∞ := by
    simpa [q] using hpConjTop
  have hp_ne_one : p ≠ 1 := by
    exact (ENNReal.HolderConjugate.ne_top_iff_ne_one (p := q) (q := p)).1 hqTop
  have hp_toReal_ge : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hpTop hp
  have hp_toReal_ne_one : p.toReal ≠ 1 := by
    intro h
    exact hp_ne_one ((ENNReal.toReal_eq_one_iff p).mp h)
  have hp_toReal_gt : 1 < p.toReal := lt_of_le_of_ne hp_toReal_ge (Ne.symm hp_toReal_ne_one)
  have hdisc : Real.HolderConjugate q.toReal p.toReal :=
    (ENNReal.HolderConjugate.toReal (p := p) (q := q) hp_toReal_gt).symm
  have hconj_q : ENNReal.conjExponent q = p := by
    simpa using (ENNReal.HolderConjugate.conjExponent_eq (p := q) (q := p))
  let h : Vec d → ℝ :=
    fun x => cubeProjection Q (j + 1) g x * cubeProjectionResidual Q j f x
  have hint_local :
      ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.IntegrableOn h (cubeSet R) MeasureTheory.volume := by
    intro R hR
    have hres :
        MeasureTheory.MemLp (cubeProjectionResidual Q j f) p (normalizedCubeMeasure R) :=
      cubeProjectionResidual_memLp_of_mem_descendantsAtDepth
        (Q := Q) (R := R) (j := j) (p := p) (u := f) hR (hf R hR)
    have hprod_norm :
        MeasureTheory.Integrable h (normalizedCubeMeasure R) := by
      simpa [h, q] using! (hg R hR).integrable_mul hres
    have hscale_ne_zero : ENNReal.ofReal ((cubeVolume R)⁻¹) ≠ 0 := by
      have hscale_pos : 0 < ENNReal.ofReal ((cubeVolume R)⁻¹) := by
        exact ENNReal.ofReal_pos.mpr (inv_pos.mpr (cubeVolume_pos R))
      exact hscale_pos.ne'
    unfold MeasureTheory.IntegrableOn
    rw [normalizedCubeMeasure, cubeMeasure] at hprod_norm
    exact (MeasureTheory.integrable_smul_measure
      (μ := MeasureTheory.volume.restrict (cubeSet R)) hscale_ne_zero ENNReal.ofReal_ne_top).1
      hprod_norm
  have hint :
      MeasureTheory.IntegrableOn h (cubeSet Q) MeasureTheory.volume := by
    rw [cubeSet_eq_iUnion_descendantsAtDepth Q j]
    exact (MeasureTheory.integrableOn_finset_iUnion
      (f := h) (μ := MeasureTheory.volume) (s := descendantsAtDepth Q j) (t := cubeSet)).2
      hint_local
  rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn (Q := Q) (j := j) (f := h) hint]
  have habs :
      |descendantsAverage Q j (fun R => cubeAverage R h)| ≤
        descendantsAverage Q j (fun R => |cubeAverage R h|) := by
    unfold descendantsAverage
    have hcard_nonneg : 0 ≤ (((descendantsAtDepth Q j).card : ℝ)⁻¹) := by positivity
    calc
      |((↑(descendantsAtDepth Q j).card)⁻¹ * ∑ R ∈ descendantsAtDepth Q j, cubeAverage R h)|
          = ((↑(descendantsAtDepth Q j).card)⁻¹) *
              |∑ R ∈ descendantsAtDepth Q j, cubeAverage R h| := by
                rw [abs_mul, abs_of_nonneg hcard_nonneg]
      _ ≤ ((↑(descendantsAtDepth Q j).card)⁻¹) *
            ∑ R ∈ descendantsAtDepth Q j, |cubeAverage R h| := by
              exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hcard_nonneg
      _ = descendantsAverage Q j (fun R => |cubeAverage R h|) := by
            rfl
  refine le_trans habs ?_
  have hlocal :
      ∀ R ∈ descendantsAtDepth Q j,
        |cubeAverage R h| ≤
          cubeLpNorm R q (cubeProjection Q (j + 1) g) * cubeBesovOscillation R p f := by
    intro R hR
    have hf' : MeasureTheory.MemLp (cubeFluctuation R f) (ENNReal.conjExponent q)
        (normalizedCubeMeasure R) := by
      simpa [hconj_q] using hf R hR
    have hlocal' :
        |cubeAverage R h| ≤
          cubeLpNorm R q (cubeProjection Q (j + 1) g) *
            cubeBesovOscillation R (ENNReal.conjExponent q) f := by
      simpa [h, q] using
        (abs_cubeAverage_mul_cubeProjectionResidual_le_mul_cubeLpNorm_cubeBesovOscillation_of_mem_descendantsAtDepth
        (Q := Q) (R := R) (j := j) (p := q) (f := cubeProjection Q (j + 1) g) (u := f)
          hR (hg R hR) hf' hq)
    simpa [hconj_q] using hlocal'
  have hpointwise :
      descendantsAverage Q j (fun R => |cubeAverage R h|) ≤
        descendantsAverage Q j (fun R =>
          cubeLpNorm R q (cubeProjection Q (j + 1) g) * cubeBesovOscillation R p f) := by
    unfold descendantsAverage
    have hcard_nonneg : 0 ≤ (((descendantsAtDepth Q j).card : ℝ)⁻¹) := by positivity
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun R hR => hlocal R hR) hcard_nonneg
  refine le_trans hpointwise ?_
  have hholder :=
    descendantsAverage_mul_le_Lp_mul_Lq_of_nonneg
      (Q := Q) (j := j)
      (A := fun R => cubeLpNorm R q (cubeProjection Q (j + 1) g))
      (B := fun R => cubeBesovOscillation R p f)
      hdisc
      (fun R hR => cubeLpNorm_nonneg R q (cubeProjection Q (j + 1) g))
      (fun R hR => cubeBesovOscillation_nonneg R p f)
  refine le_trans hholder ?_
  have hcirc :
      descendantsAverage Q j (fun R =>
        (cubeLpNorm R q (cubeProjection Q (j + 1) g)) ^ q.toReal) =
        cubeBesovCircDepthAverage Q q g (j + 1) := by
    refine descendantsAverage_cubeLpNorm_projection_succ_eq_cubeBesovCircDepthAverage
      (Q := Q) (p := q) (g := g) (j := j) (hp0 := cubeBesovConjExponent_ne_zero p)
      (hpTop := hqTop) ?_
    intro R hR
    simpa [q] using hg R hR
  rw [hcirc, cubeBesovDepthAverage]


end Homogenization
