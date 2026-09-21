/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Duality.WrapperComparison
import LeanPool.CoarseGraining.Homogenization.Multiscale.ProjectionConvergence
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Filter.AtTopBot.Basic

/-! # Projection Limit -/

namespace Homogenization

open scoped BigOperators ENNReal Topology

theorem integrableOn_cubeProjection_of_integrableOn {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (g : Vec d → ℝ) :
    MeasureTheory.IntegrableOn (cubeProjection Q j g) (cubeSet Q) MeasureTheory.volume := by
  have hlocal :
      ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.IntegrableOn (cubeProjection Q j g) (cubeSet R) MeasureTheory.volume := by
    intro R hR
    have hvol_ne_top : MeasureTheory.volume (cubeSet R) ≠ ∞ := by
      intro htop
      have hreal : (MeasureTheory.volume (cubeSet R)).toReal = cubeVolume R :=
        volume_cubeSet_toReal R
      rw [htop] at hreal
      simp at hreal
      exact (cubeVolume_pos R).ne' hreal.symm
    have hconst :
        MeasureTheory.IntegrableOn (fun _ : Vec d => cubeAverage R g) (cubeSet R)
          MeasureTheory.volume := by
      exact MeasureTheory.integrableOn_const
        (μ := MeasureTheory.volume) (s := cubeSet R) (C := cubeAverage R g) hvol_ne_top
    refine hconst.congr_fun ?_ (measurableSet_cubeSet R)
    intro x hx
    rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) g hR hx]
  rw [cubeSet_eq_iUnion_descendantsAtDepth Q j]
  exact (MeasureTheory.integrableOn_finset_iUnion
    (f := cubeProjection Q j g) (μ := MeasureTheory.volume)
    (s := descendantsAtDepth Q j) (t := cubeSet)).2 hlocal

theorem cubeProjection_abs_le_of_abs_le_on_cubeSet {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (g : Vec d → ℝ) (C : ℝ)
    (hbound : ∀ x ∈ cubeSet Q, |g x| ≤ C) :
    ∀ x ∈ cubeSet Q, |cubeProjection Q j g x| ≤ C := by
  intro x hx
  rcases exists_mem_descendantsAtDepth_of_mem_cubeSet (Q := Q) (n := j) hx with ⟨R, hR, hxR⟩
  rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth (Q := Q) (R := R) (j := j) g hR hxR]
  let μR : MeasureTheory.Measure (Vec d) := MeasureTheory.volume.restrict (cubeSet R)
  let : MeasureTheory.IsFiniteMeasure μR := by
    refine ⟨by
      simpa [μR] using lt_top_iff_ne_top.mpr (by
        intro htop
        have hreal : (MeasureTheory.volume (cubeSet R)).toReal = cubeVolume R :=
          volume_cubeSet_toReal R
        rw [htop] at hreal
        simp at hreal
        exact (cubeVolume_pos R).ne' hreal.symm)⟩
  have hboundR :
      ∀ᵐ y ∂μR, ‖g y‖ ≤ C := by
    refine (MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet R)).2 ?_
    exact Filter.Eventually.of_forall fun y hy =>
      hbound y (cubeSet_subset_of_mem_descendantsAtDepth hR hy)
  have havg :
      ‖∫ y, g y ∂ μR‖ ≤ C * μR.real Set.univ :=
    MeasureTheory.norm_integral_le_of_norm_le_const hboundR
  have havg' : |∫ y, g y ∂ μR| ≤ C * cubeVolume R := by
    simpa [μR, MeasureTheory.measureReal_def] using havg
  rw [cubeAverage]
  have hvol_inv_nonneg : 0 ≤ (cubeVolume R)⁻¹ := by
    exact inv_nonneg.mpr (cubeVolume_nonneg R)
  calc
    |(cubeVolume R)⁻¹ * ∫ y, g y ∂ μR|
        = (cubeVolume R)⁻¹ * |∫ y, g y ∂ μR| := by
            rw [abs_mul, abs_of_nonneg hvol_inv_nonneg]
    _ ≤ (cubeVolume R)⁻¹ * (C * cubeVolume R) := by
          exact mul_le_mul_of_nonneg_left havg' hvol_inv_nonneg
    _ = C := by
          field_simp [(cubeVolume_pos R).ne']

theorem cubeBesovPairing_projection_comm {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (u g : Vec d → ℝ)
    (huInt : MeasureTheory.IntegrableOn u (cubeSet Q) MeasureTheory.volume)
    (hgInt : MeasureTheory.IntegrableOn g (cubeSet Q) MeasureTheory.volume) :
    cubeBesovPairing Q (cubeProjection Q j u) g =
      cubeBesovPairing Q u (cubeProjection Q j g) := by
  let hleft : Vec d → ℝ := fun x => cubeProjection Q j u x * g x
  let hright : Vec d → ℝ := fun x => u x * cubeProjection Q j g x
  have hleft_local :
      ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.IntegrableOn hleft (cubeSet R) MeasureTheory.volume := by
    intro R hR
    have hgIntR :
        MeasureTheory.IntegrableOn g (cubeSet R) MeasureTheory.volume :=
      hgInt.mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR)
    have hconst :
        MeasureTheory.IntegrableOn (fun x => cubeAverage R u * g x) (cubeSet R)
          MeasureTheory.volume := by
      simpa [mul_comm] using! hgIntR.const_mul (cubeAverage R u)
    refine hconst.congr_fun ?_ (measurableSet_cubeSet R)
    intro x hx
    simp [hleft, cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) u hR hx]
  have hright_local :
      ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.IntegrableOn hright (cubeSet R) MeasureTheory.volume := by
    intro R hR
    have huIntR :
        MeasureTheory.IntegrableOn u (cubeSet R) MeasureTheory.volume :=
      huInt.mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR)
    have hconst :
        MeasureTheory.IntegrableOn (fun x => u x * cubeAverage R g) (cubeSet R)
          MeasureTheory.volume := by
      exact huIntR.mul_const (cubeAverage R g)
    refine hconst.congr_fun ?_ (measurableSet_cubeSet R)
    intro x hx
    simp [hright, cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) g hR hx]
  have hleft_int :
      MeasureTheory.IntegrableOn hleft (cubeSet Q) MeasureTheory.volume := by
    rw [cubeSet_eq_iUnion_descendantsAtDepth Q j]
    exact (MeasureTheory.integrableOn_finset_iUnion
      (f := hleft) (μ := MeasureTheory.volume)
      (s := descendantsAtDepth Q j) (t := cubeSet)).2 hleft_local
  have hright_int :
      MeasureTheory.IntegrableOn hright (cubeSet Q) MeasureTheory.volume := by
    rw [cubeSet_eq_iUnion_descendantsAtDepth Q j]
    exact (MeasureTheory.integrableOn_finset_iUnion
      (f := hright) (μ := MeasureTheory.volume)
      (s := descendantsAtDepth Q j) (t := cubeSet)).2 hright_local
  unfold cubeBesovPairing
  rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
    (Q := Q) (j := j) (f := fun x => cubeProjection Q j u x * g x) hleft_int]
  rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
    (Q := Q) (j := j) (f := fun x => u x * cubeProjection Q j g x) hright_int]
  unfold descendantsAverage
  refine congrArg (fun t : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
  refine Finset.sum_congr rfl ?_
  intro R hR
  have hleft_avg :
      cubeAverage R (fun x => cubeProjection Q j u x * g x) =
        cubeAverage R u * cubeAverage R g := by
    have hcongr :
        cubeAverage R (fun x => cubeProjection Q j u x * g x) =
          cubeAverage R (fun x => cubeAverage R u * g x) := by
      apply cubeAverage_congr_on_cubeSet
      intro x hx
      simp [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
        (Q := Q) (R := R) (j := j) u hR hx]
    rw [hcongr, cubeAverage_eq_integral_normalizedCubeMeasure,
      MeasureTheory.integral_const_mul, ← cubeAverage_eq_integral_normalizedCubeMeasure]
  have hright_avg :
      cubeAverage R (fun x => u x * cubeProjection Q j g x) =
        cubeAverage R u * cubeAverage R g := by
    have hcongr :
        cubeAverage R (fun x => u x * cubeProjection Q j g x) =
          cubeAverage R (fun x => u x * cubeAverage R g) := by
      apply cubeAverage_congr_on_cubeSet
      intro x hx
      simp [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
        (Q := Q) (R := R) (j := j) g hR hx]
    rw [hcongr, cubeAverage_eq_integral_normalizedCubeMeasure,
      MeasureTheory.integral_mul_const, ← cubeAverage_eq_integral_normalizedCubeMeasure]
  rw [hleft_avg, hright_avg]

theorem tendsto_cubeBesovPairing_projection_right_of_integrableOn_of_bounded {d : ℕ}
    (Q : TriadicCube d) (u g : Vec d → ℝ) (C : ℝ)
    (huInt : MeasureTheory.IntegrableOn u (cubeSet Q) MeasureTheory.volume)
    (hgInt : MeasureTheory.IntegrableOn g (cubeSet Q) MeasureTheory.volume)
    (hC : 0 ≤ C)
    (hbound : ∀ x ∈ cubeSet Q, |g x| ≤ C) :
    Filter.Tendsto (fun n => cubeBesovPairing Q u (cubeProjection Q (n + 1) g))
      Filter.atTop (𝓝 (cubeBesovPairing Q u g)) := by
  let μQ : MeasureTheory.Measure (Vec d) := MeasureTheory.volume.restrict (cubeSet Q)
  let F : ℕ → Vec d → ℝ := fun n x => u x * cubeProjection Q (n + 1) g x
  let bound : Vec d → ℝ := fun x => |u x| * C
  have hC_nonneg : 0 ≤ C := hC
  have hprojInt :
      ∀ n, MeasureTheory.IntegrableOn (cubeProjection Q (n + 1) g) (cubeSet Q)
        MeasureTheory.volume := by
    intro n
    exact integrableOn_cubeProjection_of_integrableOn Q (n + 1) g
  have hF_meas : ∀ n, MeasureTheory.AEStronglyMeasurable (F n) μQ := by
    intro n
    exact (huInt.aestronglyMeasurable.mul (hprojInt n).aestronglyMeasurable)
  have hbound_int : MeasureTheory.Integrable bound μQ := by
    simpa [bound, Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc]
      using huInt.norm.const_mul C
  have hF_bound : ∀ n, ∀ᵐ x ∂μQ, ‖F n x‖ ≤ bound x := by
    intro n
    refine (MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    have hproj :
        |cubeProjection Q (n + 1) g x| ≤ C :=
      cubeProjection_abs_le_of_abs_le_on_cubeSet Q (n + 1) g C hbound x hx
    simpa [F, bound, abs_mul, Real.norm_eq_abs, abs_of_nonneg hC_nonneg, mul_comm, mul_left_comm,
      mul_assoc] using mul_le_mul_of_nonneg_left hproj (abs_nonneg (u x))
  have hF_lim :
      ∀ᵐ x ∂μQ, Filter.Tendsto (fun n => F n x) Filter.atTop (𝓝 (u x * g x)) := by
    filter_upwards [ae_tendsto_cubeProjection_of_integrableOn (Q := Q) (f := g) hgInt] with x hx
    have hx' :
        Filter.Tendsto (fun n => cubeProjection Q (n + 1) g x) Filter.atTop (𝓝 (g x)) :=
      hx.comp (Filter.tendsto_add_atTop_nat 1)
    exact tendsto_const_nhds.mul hx'
  have hInt :
      Filter.Tendsto (fun n => ∫ x, F n x ∂ μQ) Filter.atTop
        (𝓝 (∫ x, u x * g x ∂ μQ)) :=
    MeasureTheory.tendsto_integral_of_dominated_convergence bound hF_meas hbound_int hF_bound hF_lim
  simpa [cubeBesovPairing, cubeAverage, μQ, F] using
    hInt.const_mul ((cubeVolume Q)⁻¹)

theorem tendsto_cubeBesovPairing_projection_left_of_integrableOn_of_bounded {d : ℕ}
    (Q : TriadicCube d) (u g : Vec d → ℝ) (C : ℝ)
    (huInt : MeasureTheory.IntegrableOn u (cubeSet Q) MeasureTheory.volume)
    (hgInt : MeasureTheory.IntegrableOn g (cubeSet Q) MeasureTheory.volume)
    (hC : 0 ≤ C)
    (hbound : ∀ x ∈ cubeSet Q, |g x| ≤ C) :
    Filter.Tendsto (fun n => cubeBesovPairing Q (cubeProjection Q (n + 1) u) g)
      Filter.atTop (𝓝 (cubeBesovPairing Q u g)) := by
  have hcomm :
      ∀ n, cubeBesovPairing Q (cubeProjection Q (n + 1) u) g =
        cubeBesovPairing Q u (cubeProjection Q (n + 1) g) := by
    intro n
    exact cubeBesovPairing_projection_comm Q (n + 1) u g huInt hgInt
  have hright :=
    tendsto_cubeBesovPairing_projection_right_of_integrableOn_of_bounded
      Q u g C huInt hgInt hC hbound
  convert hright using 1
  ext n
  exact hcomm n

theorem normalizedCubeMeasure_descendant_eq_smul_restrict {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j) :
    normalizedCubeMeasure R =
      ENNReal.ofReal (cubeVolume Q / cubeVolume R) •
        (normalizedCubeMeasure Q).restrict (cubeSet R) := by
  ext s hs
  have hQ : cubeVolume Q ≠ 0 := (cubeVolume_pos Q).ne'
  have hRvol : cubeVolume R ≠ 0 := (cubeVolume_pos R).ne'
  have hsubset : cubeSet R ⊆ cubeSet Q := cubeSet_subset_of_mem_descendantsAtDepth hR
  have hinter :
      (s ∩ cubeSet R) ∩ cubeSet Q = s ∩ cubeSet R := by
    ext x
    constructor
    · intro hx
      exact hx.1
    · intro hx
      exact ⟨hx, hsubset hx.2⟩
  rw [normalizedCubeMeasure, MeasureTheory.Measure.smul_apply]
  rw [cubeMeasure, MeasureTheory.Measure.restrict_apply hs]
  rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.restrict_apply hs]
  rw [normalizedCubeMeasure, MeasureTheory.Measure.smul_apply]
  change ENNReal.ofReal ((cubeVolume R)⁻¹) * MeasureTheory.volume (s ∩ cubeSet R) =
    ENNReal.ofReal (cubeVolume Q / cubeVolume R) *
      (ENNReal.ofReal ((cubeVolume Q)⁻¹) * cubeMeasure Q (s ∩ cubeSet R))
  rw [cubeMeasure, MeasureTheory.Measure.restrict_apply (hs.inter (measurableSet_cubeSet R)), hinter]
  have hfactor :
      ENNReal.ofReal ((cubeVolume R)⁻¹) =
        ENNReal.ofReal (cubeVolume Q / cubeVolume R) *
          ENNReal.ofReal ((cubeVolume Q)⁻¹) := by
    have hdiv_nonneg : 0 ≤ cubeVolume Q / cubeVolume R := by
      exact div_nonneg (cubeVolume_nonneg Q) (cubeVolume_nonneg R)
    rw [← ENNReal.ofReal_mul hdiv_nonneg]
    congr 1
    field_simp [hQ, hRvol]
  rw [hfactor, ← mul_assoc]

theorem memLp_on_descendant_of_memLp {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    {p : ℝ≥0∞} {f : Vec d → ℝ}
    (hR : R ∈ descendantsAtDepth Q j)
    (hf : MeasureTheory.MemLp f p (normalizedCubeMeasure Q)) :
    MeasureTheory.MemLp f p (normalizedCubeMeasure R) := by
  have hrestrict :
      MeasureTheory.MemLp f p ((normalizedCubeMeasure Q).restrict (cubeSet R)) :=
    hf.restrict (cubeSet R)
  have hle :
      normalizedCubeMeasure R ≤
        ENNReal.ofReal (cubeVolume Q / cubeVolume R) •
          ((normalizedCubeMeasure Q).restrict (cubeSet R)) := by
    simp [normalizedCubeMeasure_descendant_eq_smul_restrict hR]
  exact hrestrict.of_measure_le_smul ENNReal.ofReal_ne_top hle

theorem cubeBesovCircDepthAverage_le_cubeLpNorm_rpow {d : ℕ}
    (Q : TriadicCube d) (p : ℝ≥0∞) (u : Vec d → ℝ) (j : ℕ)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (hu : MeasureTheory.MemLp u p (normalizedCubeMeasure Q)) :
    cubeBesovCircDepthAverage Q p u j ≤ (cubeLpNorm Q p u) ^ p.toReal := by
  classical
  let q : ℝ≥0∞ := cubeBesovConjExponent p
  let : ENNReal.HolderConjugate p q := by
    simpa [q, cubeBesovConjExponent] using ENNReal.HolderConjugate.conjExponent hp
  have hp0 : p ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hq0 : q ≠ 0 := by
    simpa [q] using cubeBesovConjExponent_ne_zero p
  have hnorm_int :
      MeasureTheory.IntegrableOn (fun x => ‖u x‖ ^ p.toReal) (cubeSet Q)
        MeasureTheory.volume := by
    exact integrableOn_of_integrable_normalizedCubeMeasure (Q := Q)
      (hu.integrable_norm_rpow hp0 hpTop)
  calc
    cubeBesovCircDepthAverage Q p u j
        ≤ descendantsAverage Q j (fun R => (cubeLpNorm R p u) ^ p.toReal) := by
          unfold cubeBesovCircDepthAverage descendantsAverage
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · refine Finset.sum_le_sum ?_
            intro R hR
            have huR : MeasureTheory.MemLp u p (normalizedCubeMeasure R) :=
              memLp_on_descendant_of_memLp (Q := Q) (R := R) (j := j) hR hu
            have hconst :
                MeasureTheory.MemLp (fun _ : Vec d => (1 : ℝ)) q (normalizedCubeMeasure R) :=
              MeasureTheory.memLp_const (1 : ℝ)
            have havg :
                ‖cubeAverage R u‖ ≤ cubeLpNorm R p u * cubeLpNorm R q (fun _ => (1 : ℝ)) := by
              simpa [q] using!
                abs_cubeAverage_mul_le_mul_cubeLpNorm_conjExponent
                  (Q := R) (p := p) (f := u) (g := fun _ => (1 : ℝ)) huR hconst hp
            have hnorm_one : cubeLpNorm R q (fun _ => (1 : ℝ)) = 1 := by
              simpa using cubeLpNorm_const (Q := R) (p := q) (c := (1 : ℝ)) hq0
            have havg' : ‖cubeAverage R u‖ ≤ cubeLpNorm R p u := by
              simpa [hnorm_one] using havg
            exact Real.rpow_le_rpow (norm_nonneg _) havg' ENNReal.toReal_nonneg
          · positivity
    _ = descendantsAverage Q j (fun R => cubeAverage R (fun x => ‖u x‖ ^ p.toReal)) := by
          unfold descendantsAverage
          refine congrArg (fun t : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
          refine Finset.sum_congr rfl ?_
          intro R hR
          rw [← cubeLpNorm_rpow_eq_cubeAverage_norm_rpow (Q := R) (p := p) (f := u) hp0 hpTop]
          exact memLp_on_descendant_of_memLp (Q := Q) (R := R) (j := j) hR hu
    _ = cubeAverage Q (fun x => ‖u x‖ ^ p.toReal) := by
          rw [← cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
            (Q := Q) (j := j) (f := fun x => ‖u x‖ ^ p.toReal) hnorm_int]
    _ = (cubeLpNorm Q p u) ^ p.toReal := by
          symm
          rw [cubeLpNorm_rpow_eq_cubeAverage_norm_rpow (Q := Q) (p := p) (f := u) hp0 hpTop hu]

theorem cubeProjection_memLp {d : ℕ} (Q : TriadicCube d) (j : ℕ) (p : ℝ≥0∞)
    (u : Vec d → ℝ) :
    MeasureTheory.MemLp (cubeProjection Q j u) p (normalizedCubeMeasure Q) := by
  classical
  unfold cubeProjection
  refine MeasureTheory.memLp_finsetSum
    (s := descendantsAtDepth Q j)
    (f := fun R : TriadicCube d => fun x : Vec d =>
      if x ∈ cubeSet R then cubeAverage R u else 0) ?_
  intro R hR
  have hR_ne_top : normalizedCubeMeasure Q (cubeSet R) ≠ ∞ := by
    have hR_le : normalizedCubeMeasure Q (cubeSet R) ≤ normalizedCubeMeasure Q Set.univ :=
      MeasureTheory.measure_mono (Set.subset_univ (cubeSet R))
    have hUniv_lt : normalizedCubeMeasure Q Set.univ < ∞ := by simp
    exact ne_of_lt (lt_of_le_of_lt hR_le hUniv_lt)
  simpa [Set.indicator] using!
    (MeasureTheory.memLp_indicator_const (μ := normalizedCubeMeasure Q)
      (p := p) (s := cubeSet R) (hs := measurableSet_cubeSet R)
      (c := cubeAverage R u) (Or.inr hR_ne_top))

theorem cubeLpNorm_rpow_cubeProjection_eq_cubeBesovCircDepthAverage {d : ℕ}
    (Q : TriadicCube d) (p : ℝ≥0∞) (u : Vec d → ℝ) (j : ℕ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    (cubeLpNorm Q p (cubeProjection Q j u)) ^ p.toReal =
      cubeBesovCircDepthAverage Q p u j := by
  have hprojMem :
      MeasureTheory.MemLp (cubeProjection Q j u) p (normalizedCubeMeasure Q) :=
    cubeProjection_memLp Q j p u
  have hprojInt :
      MeasureTheory.IntegrableOn (fun x => ‖cubeProjection Q j u x‖ ^ p.toReal)
        (cubeSet Q) MeasureTheory.volume := by
    exact integrableOn_of_integrable_normalizedCubeMeasure (Q := Q)
      (hprojMem.integrable_norm_rpow hp0 hpTop)
  rw [cubeLpNorm_rpow_eq_cubeAverage_norm_rpow
    (Q := Q) (p := p) (f := cubeProjection Q j u) hp0 hpTop hprojMem]
  rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
    (Q := Q) (j := j) (f := fun x => ‖cubeProjection Q j u x‖ ^ p.toReal) hprojInt]
  rw [cubeBesovCircDepthAverage_eq_descendantsAverage_projection
    (Q := Q) (p := p) (u := u) (j := j) hp0]
  unfold descendantsAverage
  refine congrArg (fun t : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
  refine Finset.sum_congr rfl ?_
  intro R hR
  rw [← cubeLpNorm_rpow_eq_cubeAverage_norm_rpow
    (Q := R) (p := p) (f := cubeProjection Q j u) hp0 hpTop]
  exact cubeProjection_memLp_of_mem_descendantsAtDepth
    (Q := Q) (R := R) (j := j) p u hR

theorem cubeLpNorm_cubeProjection_le {d : ℕ}
    (Q : TriadicCube d) (p : ℝ≥0∞) (u : Vec d → ℝ) (j : ℕ)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (hu : MeasureTheory.MemLp u p (normalizedCubeMeasure Q)) :
    cubeLpNorm Q p (cubeProjection Q j u) ≤ cubeLpNorm Q p u := by
  have hp0 : p ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpReal_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  have hpow :
      (cubeLpNorm Q p (cubeProjection Q j u)) ^ p.toReal ≤
        (cubeLpNorm Q p u) ^ p.toReal := by
    rw [cubeLpNorm_rpow_cubeProjection_eq_cubeBesovCircDepthAverage
      (Q := Q) (p := p) (u := u) (j := j) hp0 hpTop]
    exact cubeBesovCircDepthAverage_le_cubeLpNorm_rpow Q p u j hp hpTop hu
  calc
    cubeLpNorm Q p (cubeProjection Q j u)
        = ((cubeLpNorm Q p (cubeProjection Q j u)) ^ p.toReal) ^ (1 / p.toReal) := by
            symm
            rw [← Real.rpow_mul (cubeLpNorm_nonneg Q p (cubeProjection Q j u))]
            field_simp [hpReal_pos.ne']
            rw [Real.rpow_one]
    _ ≤ ((cubeLpNorm Q p u) ^ p.toReal) ^ (1 / p.toReal) := by
          exact Real.rpow_le_rpow
            (Real.rpow_nonneg (cubeLpNorm_nonneg Q p (cubeProjection Q j u)) _)
            hpow
            (show 0 ≤ 1 / p.toReal by positivity)
    _ = cubeLpNorm Q p u := by
          rw [← Real.rpow_mul (cubeLpNorm_nonneg Q p u)]
          field_simp [hpReal_pos.ne']
          rw [Real.rpow_one]

theorem cubeBesovPairing_sub_right_of_integrableOn {d : ℕ}
    (Q : TriadicCube d) (f g h : Vec d → ℝ)
    (hfg : MeasureTheory.IntegrableOn (fun x => f x * g x) (cubeSet Q) MeasureTheory.volume)
    (hfh : MeasureTheory.IntegrableOn (fun x => f x * h x) (cubeSet Q) MeasureTheory.volume) :
    cubeBesovPairing Q f (fun x => g x - h x) =
      cubeBesovPairing Q f g - cubeBesovPairing Q f h := by
  unfold cubeBesovPairing cubeAverage
  rw [show (fun x => f x * (g x - h x)) = fun x => f x * g x - f x * h x by
    funext x
    ring]
  rw [MeasureTheory.integral_sub hfg hfh]
  ring

theorem tendsto_cubeBesovPairing_projection_left_of_memLp {d : ℕ}
    (Q : TriadicCube d) (p : ℝ≥0∞) (u g : Vec d → ℝ)
    (hu : MeasureTheory.MemLp u p (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (cubeBesovConjExponent p) (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) (hpConjTop : cubeBesovConjExponent p ≠ ∞) :
    Filter.Tendsto (fun n => cubeBesovPairing Q (cubeProjection Q (n + 1) u) g)
      Filter.atTop (𝓝 (cubeBesovPairing Q u g)) := by
  let q : ℝ≥0∞ := cubeBesovConjExponent p
  let : ENNReal.HolderConjugate p q := by
    simpa [q, cubeBesovConjExponent] using ENNReal.HolderConjugate.conjExponent hp
  have hq : 1 ≤ q := by
    simpa [q] using (ENNReal.HolderConjugate.one_le (p := q) (q := p))
  have huInt :
      MeasureTheory.IntegrableOn u (cubeSet Q) MeasureTheory.volume := by
    exact integrableOn_of_integrable_normalizedCubeMeasure (Q := Q) (hu.integrable hp)
  rw [Metric.tendsto_atTop]
  intro ε hε
  let M : ℝ := cubeLpNorm Q p u + 1
  let δ : ℝ := ε / (4 * M)
  have hM_pos : 0 < M := by
    unfold M
    linarith [cubeLpNorm_nonneg Q p u]
  have hδ_pos : 0 < δ := by
    unfold δ
    positivity
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
  have hM_ge : cubeLpNorm Q p u ≤ M := by
    unfold M
    linarith [cubeLpNorm_nonneg Q p u]
  have hMδ : M * δ = ε / 4 := by
    unfold δ
    field_simp [hM_pos.ne']
  obtain ⟨h, happrox, hmem⟩ :=
    MeasureTheory.MemLp.exists_boundedContinuous_eLpNorm_sub_le
      (μ := normalizedCubeMeasure Q) (p := q) (f := g) hpConjTop hg
      (ε := ENNReal.ofReal δ) (ENNReal.ofReal_ne_zero_iff.mpr hδ_pos)
  have hdiffMem :
      MeasureTheory.MemLp (fun x => g x - h x) q (normalizedCubeMeasure Q) :=
    hg.sub hmem
  have hdiffNorm : cubeLpNorm Q q (fun x => g x - h x) ≤ δ := by
    change (MeasureTheory.eLpNorm (g - ⇑h) q (normalizedCubeMeasure Q)).toReal ≤ δ
    calc
      (MeasureTheory.eLpNorm (g - ⇑h) q (normalizedCubeMeasure Q)).toReal
          ≤ (ENNReal.ofReal δ).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top happrox
      _ = δ := by
            simp [le_of_lt hδ_pos]
  have hhInt :
      MeasureTheory.IntegrableOn (h : Vec d → ℝ) (cubeSet Q) MeasureTheory.volume := by
    exact integrableOn_of_integrable_normalizedCubeMeasure (Q := Q) (hmem.integrable hq)
  have hbound : ∀ x ∈ cubeSet Q, |h x| ≤ ‖h‖ := by
    intro x _hx
    simpa [Real.norm_eq_abs] using h.norm_coe_le_norm x
  have hconv :=
    tendsto_cubeBesovPairing_projection_left_of_integrableOn_of_bounded
      Q u h ‖h‖ huInt hhInt (norm_nonneg _) hbound
  rw [Metric.tendsto_atTop] at hconv
  obtain ⟨N, hN⟩ := hconv (ε / 2) (by positivity)
  refine ⟨N, ?_⟩
  intro n hn
  have hprojMem :
      MeasureTheory.MemLp (cubeProjection Q (n + 1) u) p (normalizedCubeMeasure Q) :=
    cubeProjection_memLp Q (n + 1) p u
  have hprojNorm :
      cubeLpNorm Q p (cubeProjection Q (n + 1) u) ≤ cubeLpNorm Q p u := by
    exact cubeLpNorm_cubeProjection_le Q p u (n + 1) hp hpTop hu
  have hproj_nonneg : 0 ≤ cubeLpNorm Q p (cubeProjection Q (n + 1) u) :=
    cubeLpNorm_nonneg Q p (cubeProjection Q (n + 1) u)
  have hdiff_nonneg : 0 ≤ cubeLpNorm Q q (fun x => g x - h x) :=
    cubeLpNorm_nonneg Q q (fun x => g x - h x)
  have hprojSub :
      cubeBesovPairing Q (cubeProjection Q (n + 1) u) (fun x => g x - h x) =
        cubeBesovPairing Q (cubeProjection Q (n + 1) u) g -
          cubeBesovPairing Q (cubeProjection Q (n + 1) u) h := by
    apply cubeBesovPairing_sub_right_of_integrableOn
    · exact integrableOn_of_integrable_normalizedCubeMeasure (Q := Q)
        (hprojMem.integrable_mul hg)
    · exact integrableOn_of_integrable_normalizedCubeMeasure (Q := Q)
        (hprojMem.integrable_mul hmem)
  have huSub :
      cubeBesovPairing Q u (fun x => g x - h x) =
        cubeBesovPairing Q u g - cubeBesovPairing Q u h := by
    apply cubeBesovPairing_sub_right_of_integrableOn
    · exact integrableOn_of_integrable_normalizedCubeMeasure (Q := Q)
        (hu.integrable_mul hg)
    · exact integrableOn_of_integrable_normalizedCubeMeasure (Q := Q)
        (hu.integrable_mul hmem)
  have hprojErr :
      |cubeBesovPairing Q (cubeProjection Q (n + 1) u) g -
          cubeBesovPairing Q (cubeProjection Q (n + 1) u) h| ≤ ε / 4 := by
    rw [← hprojSub]
    calc
      |cubeBesovPairing Q (cubeProjection Q (n + 1) u) (fun x => g x - h x)|
          ≤ cubeLpNorm Q p (cubeProjection Q (n + 1) u) *
              cubeLpNorm Q q (fun x => g x - h x) := by
                simpa [q] using
                  abs_cubeBesovPairing_le_mul_cubeLpNorm_conjExponent
                    Q p (cubeProjection Q (n + 1) u) (fun x => g x - h x)
                    hprojMem hdiffMem hp
      _ ≤ cubeLpNorm Q p u * δ := by
            exact mul_le_mul hprojNorm hdiffNorm hdiff_nonneg (cubeLpNorm_nonneg Q p u)
      _ ≤ M * δ := by
            exact mul_le_mul_of_nonneg_right hM_ge hδ_nonneg
      _ = ε / 4 := by
            exact hMδ
  have huErr :
      |cubeBesovPairing Q u g - cubeBesovPairing Q u h| ≤ ε / 4 := by
    rw [← huSub]
    calc
      |cubeBesovPairing Q u (fun x => g x - h x)|
          ≤ cubeLpNorm Q p u * cubeLpNorm Q q (fun x => g x - h x) := by
                simpa [q] using
                  abs_cubeBesovPairing_le_mul_cubeLpNorm_conjExponent
                    Q p u (fun x => g x - h x) hu hdiffMem hp
      _ ≤ cubeLpNorm Q p u * δ := by
            exact mul_le_mul_of_nonneg_left hdiffNorm (cubeLpNorm_nonneg Q p u)
      _ ≤ M * δ := by
            exact mul_le_mul_of_nonneg_right hM_ge hδ_nonneg
      _ = ε / 4 := by
            exact hMδ
  let A : ℝ := cubeBesovPairing Q (cubeProjection Q (n + 1) u) g
  let B : ℝ := cubeBesovPairing Q (cubeProjection Q (n + 1) u) h
  let C : ℝ := cubeBesovPairing Q u h
  let D : ℝ := cubeBesovPairing Q u g
  have hAD : |A - D| ≤ |A - B| + |B - D| := by
    simpa [A, B, D, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (abs_add_le (A - B) (B - D))
  have hBD : |B - D| ≤ |B - C| + |C - D| := by
    simpa [B, C, D, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (abs_add_le (B - C) (C - D))
  have hmid : |B - C| < ε / 2 := by
    simpa [B, C] using! hN n hn
  have huErr' : |C - D| ≤ ε / 4 := by
    simpa [C, D, abs_sub_comm] using huErr
  have hprojErr' : |A - B| ≤ ε / 4 := by
    simpa [A, B] using hprojErr
  have : |A - D| < ε := by
    nlinarith [hAD, hBD, hmid, hprojErr', huErr']
  simpa [A, D] using! this

end Homogenization
