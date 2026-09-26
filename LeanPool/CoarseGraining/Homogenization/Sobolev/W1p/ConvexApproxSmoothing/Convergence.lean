/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.PointwiseBounds
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! # Convergence -/

@[expose] public section

namespace Homogenization

open scoped Pointwise Convolution

/-!
# L^p convergence of the convex smoothing

The `tendsto` theorems: pointwise convergence of the partial fderivs on
`contDiff` data; the matching `eLpNorm` tendstos for fderiv, for the pure
`convexApproxSmoothing u − u` difference at continuous data, then upgraded to
`MemLpOn`; and their `one_sub_mul` cutoff-weighted variants. The corresponding
statements for `unitConvexApproxSequence` close the file.
-/

theorem eventually_forall_abs_fderiv_convexApproxSmoothing_apply_basisVec_sub_le_of_contDiff
    {d : ℕ} {U : Set (Vec d)} {ρ u : Vec d → ℝ}
    (hU : IsOpenBoundedConvexDomain U) (hρ : IsConvexApproxKernel ρ) (hu : ContDiff ℝ 1 u)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 ≤ r)
    {ε : ℕ → ℝ} (hε : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hε_nonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ ε n)
    (hε_le_one : ∀ᶠ n : ℕ in Filter.atTop, ε n ≤ 1)
    (i : Fin d) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ ⦃x : Vec d⦄, x ∈ U →
      |(fderiv ℝ (convexApproxSmoothing ρ u x0 r (ε n)) x) (basisVec i) -
          (fderiv ℝ u x) (basisVec i)| ≤ δ := by
  let g : Vec d → ℝ := fun y => (fderiv ℝ u y) (basisVec i)
  have hg_cont : Continuous g := by
    simpa [g] using (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcompact : IsCompact (closure U) := hU.isBoundedDomain.isBounded.isCompact_closure
  obtain ⟨C, hC⟩ : ∃ C, ∀ t ∈ g '' closure U, ‖t‖ ≤ C := by
    exact (hcompact.image_of_continuousOn hg_cont.continuousOn).isBounded.exists_norm_le
  let M : ℝ := max C 0
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hM : ∀ y ∈ closure U, |g y| ≤ M := by
    intro y hy
    have hg_mem : g y ∈ g '' closure U := Set.mem_image_of_mem g hy
    have hCg : |g y| ≤ C := by
      simpa [Real.norm_eq_abs] using hC _ hg_mem
    exact hCg.trans (le_max_left _ _)
  have hscaled :
      Filter.Tendsto (fun n : ℕ => ε n * M) Filter.atTop (nhds 0) := by
    simpa using (hε.mul_const M)
  have hδhalf : 0 < δ / 2 := by
    linarith
  filter_upwards
    [eventually_forall_abs_convexApproxSmoothing_sub_le_of_continuous
      hU hρ hg_cont hball hr hε hε_nonneg hε_le_one hδhalf,
      Metric.tendsto_nhds.mp hscaled (δ / 2) hδhalf, hε_nonneg, hε_le_one]
      with n hn hnM hε0 hε1 x hx
  have happrox : |convexApproxSmoothing ρ g x0 r (ε n) x - g x| ≤ δ / 2 := hn hx
  have hgx : |g x| ≤ M := hM x (subset_closure hx)
  have hsmall : ε n * M ≤ δ / 2 := by
    have hlt : ε n * M < δ / 2 := by
      have hn' : |ε n * M - 0| < δ / 2 := by
        simpa [Real.dist_eq] using hnM
      simpa [abs_of_nonneg (mul_nonneg hε0 hM_nonneg)] using hn'
    exact le_of_lt hlt
  have hfirst :
      |1 - ε n| * |convexApproxSmoothing ρ g x0 r (ε n) x - g x| ≤ δ / 2 := by
    have hcoef : |1 - ε n| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hε1)]
      linarith
    calc
      |1 - ε n| * |convexApproxSmoothing ρ g x0 r (ε n) x - g x|
          ≤ 1 * |convexApproxSmoothing ρ g x0 r (ε n) x - g x| := by
              exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
      _ = |convexApproxSmoothing ρ g x0 r (ε n) x - g x| := by ring
      _ ≤ δ / 2 := happrox
  have hsecond : |ε n * g x| ≤ δ / 2 := by
    calc
      |ε n * g x| = ε n * |g x| := by
        rw [abs_mul, abs_of_nonneg hε0]
      _ ≤ ε n * M := by
          exact mul_le_mul_of_nonneg_left hgx hε0
      _ ≤ δ / 2 := hsmall
  have hdecomp :
      (1 - ε n) * convexApproxSmoothing ρ g x0 r (ε n) x - g x =
        (1 - ε n) * (convexApproxSmoothing ρ g x0 r (ε n) x - g x) - ε n * g x := by
    ring
  rw [fderiv_convexApproxSmoothing_apply_basisVec_of_contDiff hρ hu x0 r (ε n) x i, hdecomp]
  calc
    |(1 - ε n) * (convexApproxSmoothing ρ g x0 r (ε n) x - g x) - ε n * g x|
        ≤ |(1 - ε n) * (convexApproxSmoothing ρ g x0 r (ε n) x - g x)| + |ε n * g x| := by
            simpa [sub_eq_add_neg, abs_neg] using
              abs_add_le ((1 - ε n) * (convexApproxSmoothing ρ g x0 r (ε n) x - g x))
                (-(ε n * g x))
    _ = |1 - ε n| * |convexApproxSmoothing ρ g x0 r (ε n) x - g x| + |ε n * g x| := by
          rw [abs_mul]
    _ ≤ δ / 2 + δ / 2 := add_le_add hfirst hsecond
    _ = δ := by ring

theorem eventually_forall_abs_fderiv_unitConvexApproxSequence_apply_basisVec_sub_le_of_contDiff
    {d : ℕ} {U : Set (Vec d)} {u : Vec d → ℝ}
    (hU : IsOpenBoundedConvexDomain U) (hu : ContDiff ℝ 1 u)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 ≤ r)
    (i : Fin d) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ ⦃x : Vec d⦄, x ∈ U →
      |(fderiv ℝ (unitConvexApproxSequence u x0 r n) x) (basisVec i) -
          (fderiv ℝ u x) (basisVec i)| ≤ δ := by
  simpa [unitConvexApproxSequence] using!
    (eventually_forall_abs_fderiv_convexApproxSmoothing_apply_basisVec_sub_le_of_contDiff
      hU (isConvexApproxKernel_unitConvexApproxKernel (d := d)) hu hball hr
      tendsto_unitConvexApproxScale_zero
      (Filter.Eventually.of_forall unitConvexApproxScale_nonneg)
      (Filter.Eventually.of_forall unitConvexApproxScale_le_one)
      i hδ)

theorem tendsto_fderiv_unitConvexApproxSequence_apply_basisVec_of_contDiff
    {d : ℕ} {U : Set (Vec d)} {u : Vec d → ℝ}
    (hU : IsOpenBoundedConvexDomain U) (hu : ContDiff ℝ 1 u)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 ≤ r)
    (i : Fin d) {x : Vec d} (hx : x ∈ U) :
    Filter.Tendsto
      (fun n : ℕ => (fderiv ℝ (unitConvexApproxSequence u x0 r n) x) (basisVec i))
      Filter.atTop (nhds ((fderiv ℝ u x) (basisVec i))) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hδhalf : 0 < δ / 2 := by
    linarith
  filter_upwards
    [eventually_forall_abs_fderiv_unitConvexApproxSequence_apply_basisVec_sub_le_of_contDiff
      hU hu hball hr i hδhalf] with n hn
  have hbound :
      |(fderiv ℝ (unitConvexApproxSequence u x0 r n) x) (basisVec i) -
          (fderiv ℝ u x) (basisVec i)| ≤ δ / 2 := by
    exact hn hx
  have hlt :
      |(fderiv ℝ (unitConvexApproxSequence u x0 r n) x) (basisVec i) -
          (fderiv ℝ u x) (basisVec i)| < δ := by
    exact lt_of_le_of_lt hbound (by linarith)
  simpa [Real.dist_eq] using hlt

theorem tendsto_eLpNorm_fderiv_convexApproxSmoothing_apply_basisVec_sub_zero_of_contDiff
    {d : ℕ} {U : Set (Vec d)} {ρ u : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U) (hρ : IsConvexApproxKernel ρ) (hp : p ≠ ⊤)
    (hu : ContDiff ℝ 1 u)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 ≤ r)
    {ε : ℕ → ℝ} (hε : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hε_nonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ ε n)
    (hε_le_one : ∀ᶠ n : ℕ in Filter.atTop, ε n ≤ 1)
    (i : Fin d) :
    Filter.Tendsto
      (fun n : ℕ =>
        MeasureTheory.eLpNorm
          (fun x =>
            (fderiv ℝ (convexApproxSmoothing ρ u x0 r (ε n)) x) (basisVec i) -
              (fderiv ℝ u x) (basisVec i))
          p (MeasureTheory.volume.restrict U))
      Filter.atTop (nhds 0) := by
  let f : ℕ → Vec d → ℝ := fun n x =>
    (fderiv ℝ (convexApproxSmoothing ρ u x0 r (ε n)) x) (basisVec i) -
      (fderiv ℝ u x) (basisVec i)
  let μ := MeasureTheory.volume.restrict U
  let : MeasureTheory.IsFiniteMeasure μ := hU.isFiniteMeasure_restrict_volume
  have hU_meas : MeasurableSet U := hU.isOpen.measurableSet
  have hpow_ne_top : μ Set.univ ^ (1 / p.toReal) ≠ ⊤ := by
    refine (ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_).ne
    exact (MeasureTheory.measure_lt_top μ Set.univ).ne
  let cμ : ℝ := (μ Set.univ ^ (1 / p.toReal)).toReal
  have hpow_eq : ENNReal.ofReal cμ = μ Set.univ ^ (1 / p.toReal) := by
    dsimp [cμ]
    exact ENNReal.ofReal_toReal hpow_ne_top
  have hcμ_nonneg : 0 ≤ cμ := by
    exact ENNReal.toReal_nonneg
  apply ENNReal.tendsto_nhds_zero.2
  intro η hη
  by_cases hηtop : η = ⊤
  · exact Filter.Eventually.of_forall (fun n => by
      simp [hηtop])
  let δ : ℝ := η.toReal / (cμ + 1)
  have hηreal : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηtop
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  filter_upwards
    [eventually_forall_abs_fderiv_convexApproxSmoothing_apply_basisVec_sub_le_of_contDiff
      hU hρ hu hball hr hε hε_nonneg hε_le_one i hδpos] with n hn
  have hdist :
      ∀ x,
        dist
            (Set.indicator U (f n) x) 0 ≤ δ := by
    intro x
    by_cases hx : x ∈ U
    · simpa [f, hx, Real.dist_eq] using hn hx
    · simp [hx, δ, hδpos.le]
  let g : Vec d → ℝ := Set.indicator U (f n)
  have hsupport_g : Function.support g ⊆ U := by
    simp [g]
  have hnorm_indicator_sub :
      MeasureTheory.eLpNorm (g - fun _ : Vec d => (0 : ℝ)) p MeasureTheory.volume ≤
        ENNReal.ofReal δ * MeasureTheory.volume U ^ (1 / p.toReal) := by
    exact
      MeasureTheory.eLpNorm_sub_le_of_dist_bdd
        (μ := MeasureTheory.volume) (p := p) (s := U) hp hU_meas.nullMeasurableSet hδpos.le
        (by
          have hf : Measurable (f n) := by
            exact (measurable_fderiv_apply_const ℝ _ (basisVec i)).sub
              (measurable_fderiv_apply_const ℝ _ (basisVec i))
          exact (hf.indicator hU_meas).aestronglyMeasurable.sub MeasureTheory.aestronglyMeasurable_const)
        hdist hsupport_g (by simp : Function.support (fun _ : Vec d => (0 : ℝ)) ⊆ U)
  have hsub_zero : (g - fun _ : Vec d => (0 : ℝ)) = g := by
    ext x
    simp [g]
  have hnorm_indicator :
      MeasureTheory.eLpNorm g p MeasureTheory.volume ≤
        ENNReal.ofReal δ * MeasureTheory.volume U ^ (1 / p.toReal) := by
    rw [← hsub_zero]
    exact hnorm_indicator_sub
  have hnorm :
      MeasureTheory.eLpNorm (f n) p μ ≤
        ENNReal.ofReal δ * μ Set.univ ^ (1 / p.toReal) := by
    calc
      MeasureTheory.eLpNorm (f n) p μ = MeasureTheory.eLpNorm g p MeasureTheory.volume := by
            symm
            simpa [μ] using
              (MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict
                (μ := MeasureTheory.volume) (p := p) (f := f n) hU_meas)
      _ ≤ ENNReal.ofReal δ * MeasureTheory.volume U ^ (1 / p.toReal) := hnorm_indicator
      _ = ENNReal.ofReal δ * μ Set.univ ^ (1 / p.toReal) := by
            simp [μ]
  have hδmul : δ * cμ ≤ η.toReal := by
    have hfrac_le : cμ / (cμ + 1) ≤ 1 := by
      have hcμ_le : cμ ≤ cμ + 1 := by linarith
      have hden_nonneg : 0 ≤ cμ + 1 := by linarith
      simpa using (div_le_one_of_le₀ hcμ_le hden_nonneg)
    calc
      δ * cμ = η.toReal * (cμ / (cμ + 1)) := by
        dsimp [δ]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      _ ≤ η.toReal * 1 := by
            exact mul_le_mul_of_nonneg_left hfrac_le hηreal.le
      _ = η.toReal := by ring
  calc
    MeasureTheory.eLpNorm (f n) p μ ≤ ENNReal.ofReal δ * μ Set.univ ^ (1 / p.toReal) :=
      hnorm
    _ = ENNReal.ofReal (δ * cμ) := by
          rw [← hpow_eq, ← ENNReal.ofReal_mul]
          positivity
    _ ≤ η := by
          rw [← ENNReal.ofReal_toReal hηtop]
          exact ENNReal.ofReal_le_ofReal hδmul

theorem tendsto_eLpNorm_fderiv_unitConvexApproxSequence_apply_basisVec_sub_zero_of_contDiff
    {d : ℕ} {U : Set (Vec d)} {u : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U) (hp : p ≠ ⊤) (hu : ContDiff ℝ 1 u)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 ≤ r)
    (i : Fin d) :
    Filter.Tendsto
      (fun n : ℕ =>
        MeasureTheory.eLpNorm
          (fun x =>
            (fderiv ℝ (unitConvexApproxSequence u x0 r n) x) (basisVec i) -
              (fderiv ℝ u x) (basisVec i))
          p (MeasureTheory.volume.restrict U))
      Filter.atTop (nhds 0) := by
  simpa [unitConvexApproxSequence] using!
    (tendsto_eLpNorm_fderiv_convexApproxSmoothing_apply_basisVec_sub_zero_of_contDiff
      hU (isConvexApproxKernel_unitConvexApproxKernel (d := d)) hp hu hball hr
      tendsto_unitConvexApproxScale_zero
      (Filter.Eventually.of_forall unitConvexApproxScale_nonneg)
      (Filter.Eventually.of_forall unitConvexApproxScale_le_one)
      i)

theorem tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_continuous
    {d : ℕ} {U : Set (Vec d)} {ρ u : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U) (hρ : IsConvexApproxKernel ρ) (hp : p ≠ ⊤)
    (hu : Continuous u)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 ≤ r)
    {ε : ℕ → ℝ} (hε : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hε_nonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ ε n)
    (hε_le_one : ∀ᶠ n : ℕ in Filter.atTop, ε n ≤ 1) :
    Filter.Tendsto
      (fun n : ℕ =>
        MeasureTheory.eLpNorm
          (fun x => convexApproxSmoothing ρ u x0 r (ε n) x - u x)
          p (MeasureTheory.volume.restrict U))
      Filter.atTop (nhds 0) := by
  let f : ℕ → Vec d → ℝ := fun n x => convexApproxSmoothing ρ u x0 r (ε n) x - u x
  let μ := MeasureTheory.volume.restrict U
  let : MeasureTheory.IsFiniteMeasure μ := hU.isFiniteMeasure_restrict_volume
  have hU_meas : MeasurableSet U := hU.isOpen.measurableSet
  have hpow_ne_top : μ Set.univ ^ (1 / p.toReal) ≠ ⊤ := by
    refine (ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_).ne
    exact (MeasureTheory.measure_lt_top μ Set.univ).ne
  let cμ : ℝ := (μ Set.univ ^ (1 / p.toReal)).toReal
  have hcμ_nonneg : 0 ≤ cμ := by
    exact ENNReal.toReal_nonneg
  have hpow_eq : ENNReal.ofReal cμ = μ Set.univ ^ (1 / p.toReal) := by
    dsimp [cμ]
    exact ENNReal.ofReal_toReal hpow_ne_top
  apply ENNReal.tendsto_nhds_zero.2
  intro η hη
  by_cases hηtop : η = ⊤
  · exact Filter.Eventually.of_forall (fun n => by
      simp [hηtop])
  let δ : ℝ := η.toReal / (cμ + 1)
  have hηreal : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηtop
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  filter_upwards
    [eventually_forall_abs_convexApproxSmoothing_sub_le_of_continuous
      hU hρ hu hball hr hε hε_nonneg hε_le_one hδpos] with n hn
  have hdist :
      ∀ x,
        dist
            (Set.indicator U (f n) x) 0 ≤ δ := by
    intro x
    by_cases hx : x ∈ U
    · simpa [f, hx, Real.dist_eq] using hn hx
    · simp [hx, δ, hδpos.le]
  let g : Vec d → ℝ := Set.indicator U (f n)
  have hsupport_g : Function.support g ⊆ U := by
    simp [g]
  have hnorm_indicator_sub :
      MeasureTheory.eLpNorm (g - fun _ : Vec d => (0 : ℝ)) p MeasureTheory.volume ≤
        ENNReal.ofReal δ * MeasureTheory.volume U ^ (1 / p.toReal) := by
    exact
      MeasureTheory.eLpNorm_sub_le_of_dist_bdd
        (μ := MeasureTheory.volume) (p := p) (s := U) hp hU_meas.nullMeasurableSet hδpos.le
        (by
          have hf : Continuous (f n) :=
            (continuous_convexApproxSmoothing hρ.continuous hρ.compactSupport hu
              x0 r (ε n)).sub hu
          exact (hf.measurable.indicator hU_meas).aestronglyMeasurable.sub
            MeasureTheory.aestronglyMeasurable_const)
        hdist hsupport_g (by simp : Function.support (fun _ : Vec d => (0 : ℝ)) ⊆ U)
  have hsub_zero : (g - fun _ : Vec d => (0 : ℝ)) = g := by
    ext x
    simp [g]
  have hnorm_indicator :
      MeasureTheory.eLpNorm g p MeasureTheory.volume ≤
        ENNReal.ofReal δ * MeasureTheory.volume U ^ (1 / p.toReal) := by
    rw [← hsub_zero]
    exact hnorm_indicator_sub
  have hnorm :
      MeasureTheory.eLpNorm (f n) p μ ≤
        ENNReal.ofReal δ * μ Set.univ ^ (1 / p.toReal) := by
    calc
      MeasureTheory.eLpNorm (f n) p μ = MeasureTheory.eLpNorm g p MeasureTheory.volume := by
            symm
            simpa [μ] using
              (MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict
                (μ := MeasureTheory.volume) (p := p) (f := f n) hU_meas)
      _ ≤ ENNReal.ofReal δ * MeasureTheory.volume U ^ (1 / p.toReal) := hnorm_indicator
      _ = ENNReal.ofReal δ * μ Set.univ ^ (1 / p.toReal) := by
            simp [μ]
  have hδmul : δ * cμ ≤ η.toReal := by
    have hfrac_le : cμ / (cμ + 1) ≤ 1 := by
      have hcμ_le : cμ ≤ cμ + 1 := by linarith
      have hden_nonneg : 0 ≤ cμ + 1 := by linarith
      simpa using (div_le_one_of_le₀ hcμ_le hden_nonneg)
    calc
      δ * cμ = η.toReal * (cμ / (cμ + 1)) := by
        dsimp [δ]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      _ ≤ η.toReal * 1 := by
            exact mul_le_mul_of_nonneg_left hfrac_le hηreal.le
      _ = η.toReal := by ring
  calc
    MeasureTheory.eLpNorm (f n) p μ ≤ ENNReal.ofReal δ * μ Set.univ ^ (1 / p.toReal) :=
      hnorm
    _ = ENNReal.ofReal (δ * cμ) := by
          rw [← hpow_eq, ← ENNReal.ofReal_mul]
          positivity
    _ ≤ η := by
          rw [← ENNReal.ofReal_toReal hηtop]
          exact ENNReal.ofReal_le_ofReal hδmul

theorem tendsto_eLpNorm_sub_zero_unitConvexApproxSequence_of_continuous
    {d : ℕ} {U : Set (Vec d)} {u : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U) (hp : p ≠ ⊤) (hu : Continuous u)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 ≤ r) :
    Filter.Tendsto
      (fun n : ℕ =>
        MeasureTheory.eLpNorm
          (fun x => unitConvexApproxSequence u x0 r n x - u x)
          p (MeasureTheory.volume.restrict U))
      Filter.atTop (nhds 0) := by
  simpa [unitConvexApproxSequence] using
    (tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_continuous
      hU (isConvexApproxKernel_unitConvexApproxKernel (d := d)) hp hu hball hr
      tendsto_unitConvexApproxScale_zero
      (Filter.Eventually.of_forall unitConvexApproxScale_nonneg)
      (Filter.Eventually.of_forall unitConvexApproxScale_le_one))

theorem tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_memLpOn
    {d : ℕ} {U : Set (Vec d)} {ρ u : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U) (hρ : IsConvexApproxKernel ρ)
    (hp1 : 1 ≤ p) (hp : p ≠ ⊤) (hu : MemLpOn U p u)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r)
    {ε : ℕ → ℝ} (hε : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hε_pos : ∀ᶠ n : ℕ in Filter.atTop, 0 < ε n)
    (hε_lt_one : ∀ᶠ n : ℕ in Filter.atTop, ε n < 1) :
    Filter.Tendsto
      (fun n : ℕ =>
        MeasureTheory.eLpNorm
          (fun x => convexApproxSmoothing ρ u x0 r (ε n) x - u x)
          p (MeasureTheory.volume.restrict U))
      Filter.atTop (nhds 0) := by
  let μ := MeasureTheory.volume.restrict U
  apply ENNReal.tendsto_nhds_zero.2
  intro η hη
  by_cases hηtop : η = ⊤
  · exact Filter.Eventually.of_forall (fun n => by simp [hηtop])
  obtain ⟨η₁, hη₁_pos, hη₁⟩ :=
    MeasureTheory.exists_Lp_half (μ := μ) (ε := ℝ) (p := p) hη.ne'
  obtain ⟨η₂, hη₂_pos, hη₂⟩ :=
    MeasureTheory.exists_Lp_half (μ := μ) (ε := ℝ) (p := p) hη₁_pos.ne'
  have hε_nonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ ε n := by
    exact hε_pos.mono (fun _ hn => le_of_lt hn)
  have hε_le_one : ∀ᶠ n : ℕ in Filter.atTop, ε n ≤ 1 := by
    exact hε_lt_one.mono (fun _ hn => le_of_lt hn)
  have hε_lt_half : ∀ᶠ n : ℕ in Filter.atTop, ε n < (1 / 2 : ℝ) := by
    exact (tendsto_order.1 hε).2 _ (by positivity)
  let C : ENNReal := ENNReal.ofReal (((1 / 2 : ℝ) ^ d)⁻¹) ^ (1 / p).toReal
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  have hC_ne_zero : C ≠ 0 := ne_of_gt hC_pos
  have hC_ne_top : C ≠ ⊤ := by
    dsimp [C]
    exact (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top).ne
  let δ : ENNReal := min η₂ (η₁ / C)
  have hδ_pos : 0 < δ := by
    have hη₁_div_pos : 0 < η₁ / C := ENNReal.div_pos hη₁_pos.ne' hC_ne_top
    dsimp [δ]
    exact lt_min hη₂_pos hη₁_div_pos
  have huMem : MeasureTheory.MemLp u p μ := by
    simpa [μ, MemLpOn] using hu
  obtain ⟨g, happrox, hmem⟩ :=
    huMem.exists_boundedContinuous_eLpNorm_sub_le hp (ε := δ) hδ_pos.ne'
  have hthird_mem :
      MeasureTheory.MemLp (fun x => (g : Vec d → ℝ) x - u x) p μ := by
    exact hmem.sub hu
  have hthird_norm :
      MeasureTheory.eLpNorm (fun x => (g : Vec d → ℝ) x - u x) p μ ≤ η₂ := by
    have hthird_eq :
        MeasureTheory.eLpNorm (fun x => (g : Vec d → ℝ) x - u x) p μ =
          MeasureTheory.eLpNorm (fun x => u x - (g : Vec d → ℝ) x) p μ := by
      calc
        MeasureTheory.eLpNorm (fun x => (g : Vec d → ℝ) x - u x) p μ
            = MeasureTheory.eLpNorm (fun x => -((g : Vec d → ℝ) x - u x)) p μ := by
                symm
                exact
                  MeasureTheory.eLpNorm_neg
                    (fun x => (g : Vec d → ℝ) x - u x) (p := p) (μ := μ)
        _ = MeasureTheory.eLpNorm (fun x => u x - (g : Vec d → ℝ) x) p μ := by
              congr 1
              ext x
              ring
    calc
      MeasureTheory.eLpNorm (fun x => (g : Vec d → ℝ) x - u x) p μ
          = MeasureTheory.eLpNorm (fun x => u x - (g : Vec d → ℝ) x) p μ := hthird_eq
      _ ≤ δ := happrox
      _ ≤ η₂ := min_le_left _ _
  have hmid_tendsto :
      Filter.Tendsto
        (fun n : ℕ =>
          MeasureTheory.eLpNorm
            (fun x => convexApproxSmoothing ρ (g : Vec d → ℝ) x0 r (ε n) x - g x)
            p μ)
        Filter.atTop (nhds 0) := by
    exact
      tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_continuous
        hU hρ hp g.continuous hball hr.le hε hε_nonneg hε_le_one
  have hmid_eventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        MeasureTheory.eLpNorm
          (fun x => convexApproxSmoothing ρ (g : Vec d → ℝ) x0 r (ε n) x - g x)
          p μ ≤ η₂ := by
    exact ENNReal.tendsto_nhds_zero.1 hmid_tendsto η₂ hη₂_pos
  have hcombo_eventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        MeasureTheory.eLpNorm
          (fun x =>
            (convexApproxSmoothing ρ (g : Vec d → ℝ) x0 r (ε n) x - g x) +
              ((g : Vec d → ℝ) x - u x))
          p μ < η₁ := by
    filter_upwards [hmid_eventually] with n hmid
    have hmid_meas :
        MeasureTheory.AEStronglyMeasurable
          (fun x => convexApproxSmoothing ρ (g : Vec d → ℝ) x0 r (ε n) x - g x) μ := by
      exact
        ((continuous_convexApproxSmoothing hρ.continuous hρ.compactSupport g.continuous
          x0 r (ε n)).sub g.continuous).aestronglyMeasurable
    exact hη₂ _ _ hmid hthird_norm
  have hfirst_eventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        MeasureTheory.eLpNorm
          (fun x =>
            convexApproxSmoothing ρ u x0 r (ε n) x -
              convexApproxSmoothing ρ (g : Vec d → ℝ) x0 r (ε n) x)
          p μ ≤ η₁ := by
    filter_upwards [hε_pos, hε_lt_half] with n hεn_pos hεn_half
    have hfactor_le :
        ENNReal.ofReal (((1 - ε n) ^ d)⁻¹) ^ (1 / p).toReal ≤ C := by
      have hhalf_le : (1 / 2 : ℝ) ≤ 1 - ε n := by linarith
      have hpow_le : (1 / 2 : ℝ) ^ d ≤ (1 - ε n) ^ d := by
        exact pow_le_pow_left₀ (by positivity) hhalf_le d
      have hpow_half_pos : 0 < (1 / 2 : ℝ) ^ d := by positivity
      have hinv_le : ((1 - ε n) ^ d)⁻¹ ≤ ((1 / 2 : ℝ) ^ d)⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hpow_half_pos hpow_le
      have hofReal_le :
          ENNReal.ofReal (((1 - ε n) ^ d)⁻¹) ≤ ENNReal.ofReal (((1 / 2 : ℝ) ^ d)⁻¹) := by
        exact ENNReal.ofReal_le_ofReal hinv_le
      exact ENNReal.rpow_le_rpow hofReal_le (by positivity)
    have hεn_lt_one : ε n < 1 := by linarith
    have happrox' :
        MeasureTheory.eLpNorm (fun x => u x - (g : Vec d → ℝ) x) p μ ≤ δ := by
      simpa using! happrox
    calc
      MeasureTheory.eLpNorm
          (fun x =>
            convexApproxSmoothing ρ u x0 r (ε n) x -
              convexApproxSmoothing ρ (g : Vec d → ℝ) x0 r (ε n) x)
          p μ
        ≤ ENNReal.ofReal (((1 - ε n) ^ d)⁻¹) ^ (1 / p).toReal *
            MeasureTheory.eLpNorm (fun x => u x - (g : Vec d → ℝ) x) p μ := by
              exact
                eLpNorm_sub_convexApproxSmoothing_le
                  hU hρ hp1 hp hu hmem hball hr hεn_pos hεn_lt_one
      _ ≤ ENNReal.ofReal (((1 - ε n) ^ d)⁻¹) ^ (1 / p).toReal * δ := by
            gcongr
      _ ≤ C * δ := by
            gcongr
      _ ≤ C * (η₁ / C) := by
            gcongr
            exact min_le_right _ _
      _ = η₁ := by
            rw [ENNReal.mul_div_cancel hC_ne_zero hC_ne_top]
  filter_upwards [hε_pos, hε_lt_half, hfirst_eventually, hcombo_eventually] with
      n hεn_pos hεn_half hfirst hcombo
  let F : Vec d → ℝ := fun x =>
    convexApproxSmoothing ρ u x0 r (ε n) x -
      convexApproxSmoothing ρ (g : Vec d → ℝ) x0 r (ε n) x
  let G : Vec d → ℝ := fun x =>
    (convexApproxSmoothing ρ (g : Vec d → ℝ) x0 r (ε n) x - g x) +
      ((g : Vec d → ℝ) x - u x)
  have hεn_lt_one : ε n < 1 := by linarith
  have hF_meas : MeasureTheory.AEStronglyMeasurable F μ := by
    dsimp [F]
    exact
      (aestronglyMeasurable_convexApproxSmoothing
        hU hρ hp1 hu hball hr hεn_pos hεn_lt_one).sub
        ((continuous_convexApproxSmoothing hρ.continuous hρ.compactSupport g.continuous
          x0 r (ε n)).aestronglyMeasurable)
  have hG_meas : MeasureTheory.AEStronglyMeasurable G μ := by
    dsimp [G]
    exact
      (((continuous_convexApproxSmoothing hρ.continuous hρ.compactSupport g.continuous
        x0 r (ε n)).sub g.continuous).aestronglyMeasurable).add
        hthird_mem.aestronglyMeasurable
  have hsum : MeasureTheory.eLpNorm (F + G) p μ < η := by
    exact hη₁ _ _ hfirst (le_of_lt hcombo)
  have hdecomp :
      MeasureTheory.eLpNorm (fun x => convexApproxSmoothing ρ u x0 r (ε n) x - u x) p μ =
        MeasureTheory.eLpNorm (F + G) p μ := by
    apply MeasureTheory.eLpNorm_congr_ae
    filter_upwards with x
    dsimp [F, G]
    ring
  calc
    MeasureTheory.eLpNorm (fun x => convexApproxSmoothing ρ u x0 r (ε n) x - u x) p μ
      = MeasureTheory.eLpNorm (F + G) p μ := hdecomp
    _ ≤ η := hsum.le

theorem tendsto_eLpNorm_sub_zero_one_sub_mul_convexApproxSmoothing_of_memLpOn
    {d : ℕ} {U : Set (Vec d)} {ρ u : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U) (hρ : IsConvexApproxKernel ρ)
    (hp1 : 1 ≤ p) (hp : p ≠ ⊤) (hu : MemLpOn U p u)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r)
    {ε : ℕ → ℝ} (hε : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hε_pos : ∀ᶠ n : ℕ in Filter.atTop, 0 < ε n)
    (hε_lt_one : ∀ᶠ n : ℕ in Filter.atTop, ε n < 1) :
    Filter.Tendsto
      (fun n : ℕ =>
        MeasureTheory.eLpNorm
          (fun x => (1 - ε n) * convexApproxSmoothing ρ u x0 r (ε n) x - u x)
          p (MeasureTheory.volume.restrict U))
      Filter.atTop (nhds 0) := by
  let μ := MeasureTheory.volume.restrict U
  apply ENNReal.tendsto_nhds_zero.2
  intro η hη
  by_cases hηtop : η = ⊤
  · exact Filter.Eventually.of_forall (fun n => by simp [hηtop])
  obtain ⟨η₁, hη₁_pos, hη₁⟩ :=
    MeasureTheory.exists_Lp_half (μ := μ) (ε := ℝ) (p := p) hη.ne'
  have hvalue_tendsto :
      Filter.Tendsto
        (fun n : ℕ =>
          MeasureTheory.eLpNorm
            (fun x => convexApproxSmoothing ρ u x0 r (ε n) x - u x)
            p μ)
        Filter.atTop (nhds 0) :=
    tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_memLpOn
      hU hρ hp1 hp hu hball hr hε hε_pos hε_lt_one
  have hvalue_eventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        MeasureTheory.eLpNorm
          (fun x => convexApproxSmoothing ρ u x0 r (ε n) x - u x)
          p μ ≤ η₁ := by
    exact ENNReal.tendsto_nhds_zero.1 hvalue_tendsto η₁ hη₁_pos
  have hε_lt_half : ∀ᶠ n : ℕ in Filter.atTop, ε n < (1 / 2 : ℝ) := by
    exact (tendsto_order.1 hε).2 _ (by positivity)
  let C : ENNReal := ENNReal.ofReal (((1 / 2 : ℝ) ^ d)⁻¹) ^ (1 / p).toReal
  let B : ENNReal := C * MeasureTheory.eLpNorm u p μ
  have hC_ne_top : C ≠ ⊤ := by
    dsimp [C]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top |>.ne
  have hB_ne_top : B ≠ ⊤ := by
    dsimp [B]
    exact ENNReal.mul_ne_top hC_ne_top hu.eLpNorm_ne_top
  let M : ℝ := B.toReal
  have hM_eq : ENNReal.ofReal M = B := by
    dsimp [M]
    exact ENNReal.ofReal_toReal hB_ne_top
  have hM_nonneg : 0 ≤ M := ENNReal.toReal_nonneg
  have hscaled_tendsto :
      Filter.Tendsto (fun n : ℕ => |ε n| * M) Filter.atTop (nhds 0) := by
    simpa [Real.norm_eq_abs] using (hε.norm.mul_const M)
  have hsmall_tendsto :
      Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (|ε n| * M)) Filter.atTop (nhds 0) :=
    by simpa using ENNReal.tendsto_ofReal hscaled_tendsto
  have hsmall_eventually :
      ∀ᶠ n : ℕ in Filter.atTop, ENNReal.ofReal (|ε n| * M) ≤ η₁ := by
    exact ENNReal.tendsto_nhds_zero.1 hsmall_tendsto η₁ hη₁_pos
  have hconv_bound_eventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        MeasureTheory.eLpNorm (convexApproxSmoothing ρ u x0 r (ε n)) p μ ≤ B := by
    filter_upwards [hε_pos, hε_lt_half] with n hεn_pos hεn_half
    have hfactor_le :
        ENNReal.ofReal (((1 - ε n) ^ d)⁻¹) ^ (1 / p).toReal ≤ C := by
      have hhalf_le : (1 / 2 : ℝ) ≤ 1 - ε n := by linarith
      have hpow_le : (1 / 2 : ℝ) ^ d ≤ (1 - ε n) ^ d := by
        exact pow_le_pow_left₀ (by positivity) hhalf_le d
      have hpow_half_pos : 0 < (1 / 2 : ℝ) ^ d := by positivity
      have hinv_le : ((1 - ε n) ^ d)⁻¹ ≤ ((1 / 2 : ℝ) ^ d)⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hpow_half_pos hpow_le
      have hofReal_le :
          ENNReal.ofReal (((1 - ε n) ^ d)⁻¹) ≤ ENNReal.ofReal (((1 / 2 : ℝ) ^ d)⁻¹) := by
        exact ENNReal.ofReal_le_ofReal hinv_le
      exact ENNReal.rpow_le_rpow hofReal_le (by positivity)
    have hεn_lt_one : ε n < 1 := by linarith
    calc
      MeasureTheory.eLpNorm (convexApproxSmoothing ρ u x0 r (ε n)) p μ
        ≤ ENNReal.ofReal (((1 - ε n) ^ d)⁻¹) ^ (1 / p).toReal *
            MeasureTheory.eLpNorm u p μ := by
              exact eLpNorm_convexApproxSmoothing_le hU hρ hp1 hp hu hball hr hεn_pos hεn_lt_one
      _ ≤ C * MeasureTheory.eLpNorm u p μ := by
            gcongr
      _ = B := by rfl
  filter_upwards [hvalue_eventually, hconv_bound_eventually, hsmall_eventually, hε_pos, hε_lt_half] with
      n hvalue hconv_bound hsmall hεn_pos hεn_half
  let F : Vec d → ℝ := fun x => convexApproxSmoothing ρ u x0 r (ε n) x - u x
  let G : Vec d → ℝ := fun x => (-ε n) * convexApproxSmoothing ρ u x0 r (ε n) x
  have hεn_lt_one : ε n < 1 := by
    linarith
  have hF_meas : MeasureTheory.AEStronglyMeasurable F μ := by
    dsimp [F]
    exact
      (aestronglyMeasurable_convexApproxSmoothing
        hU hρ hp1 hu hball hr hεn_pos hεn_lt_one).sub hu.aestronglyMeasurable
  have hG_meas : MeasureTheory.AEStronglyMeasurable G μ := by
    dsimp [G]
    exact
      (aestronglyMeasurable_convexApproxSmoothing
        hU hρ hp1 hu hball hr hεn_pos hεn_lt_one).const_mul (-ε n)
  have hG_norm :
      MeasureTheory.eLpNorm G p μ ≤ η₁ := by
    calc
      MeasureTheory.eLpNorm G p μ
        = ENNReal.ofReal |ε n| *
            MeasureTheory.eLpNorm (convexApproxSmoothing ρ u x0 r (ε n)) p μ := by
              dsimp [G]
              change MeasureTheory.eLpNorm ((-ε n) • convexApproxSmoothing ρ u x0 r (ε n)) p μ =
                ENNReal.ofReal |ε n| *
                  MeasureTheory.eLpNorm (convexApproxSmoothing ρ u x0 r (ε n)) p μ
              simpa [Real.enorm_eq_ofReal_abs] using
                (MeasureTheory.eLpNorm_const_smul (-ε n)
                  (convexApproxSmoothing ρ u x0 r (ε n)) p μ)
      _ ≤ ENNReal.ofReal |ε n| * B := by
            gcongr
      _ = ENNReal.ofReal (|ε n| * M) := by
            rw [← hM_eq, ← ENNReal.ofReal_mul]
            positivity
      _ ≤ η₁ := hsmall
  have hsum : MeasureTheory.eLpNorm (F + G) p μ < η := by
    exact hη₁ _ _ hvalue hG_norm
  have hdecomp :
      MeasureTheory.eLpNorm
          (fun x => (1 - ε n) * convexApproxSmoothing ρ u x0 r (ε n) x - u x)
          p μ =
        MeasureTheory.eLpNorm (F + G) p μ := by
    apply MeasureTheory.eLpNorm_congr_ae
    filter_upwards with x
    dsimp [F, G]
    ring
  calc
    MeasureTheory.eLpNorm
        (fun x => (1 - ε n) * convexApproxSmoothing ρ u x0 r (ε n) x - u x)
        p μ
      = MeasureTheory.eLpNorm (F + G) p μ := hdecomp
    _ ≤ η := hsum.le

theorem tendsto_eLpNorm_sub_zero_unitConvexApproxSequence_of_memLpOn
    {d : ℕ} {U : Set (Vec d)} {u : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    (hu : MemLpOn U p u)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) :
    Filter.Tendsto
      (fun n : ℕ =>
        MeasureTheory.eLpNorm
          (fun x => unitConvexApproxSequence u x0 r n x - u x)
          p (MeasureTheory.volume.restrict U))
      Filter.atTop (nhds 0) := by
  simpa [unitConvexApproxSequence] using
    (tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_memLpOn
      hU (isConvexApproxKernel_unitConvexApproxKernel (d := d)) hp1 hp hu hball hr
      tendsto_unitConvexApproxScale_zero
      (Filter.Eventually.of_forall (fun _ => by
        dsimp [unitConvexApproxScale]
        positivity))
      (((tendsto_order.1 tendsto_unitConvexApproxScale_zero).2 1 zero_lt_one).mono
        (fun _ hn => hn)))

theorem tendsto_eLpNorm_sub_zero_one_sub_mul_unitConvexApproxSequence_of_memLpOn
    {d : ℕ} {U : Set (Vec d)} {u : Vec d → ℝ} {p : ENNReal}
    (hU : IsOpenBoundedConvexDomain U) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    (hu : MemLpOn U p u)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) :
    Filter.Tendsto
      (fun n : ℕ =>
        MeasureTheory.eLpNorm
          (fun x => (1 - unitConvexApproxScale n) * unitConvexApproxSequence u x0 r n x - u x)
          p (MeasureTheory.volume.restrict U))
      Filter.atTop (nhds 0) := by
  simpa [unitConvexApproxSequence] using
    (tendsto_eLpNorm_sub_zero_one_sub_mul_convexApproxSmoothing_of_memLpOn
      hU (isConvexApproxKernel_unitConvexApproxKernel (d := d)) hp1 hp hu hball hr
      tendsto_unitConvexApproxScale_zero
      (Filter.Eventually.of_forall (fun _ => by
        dsimp [unitConvexApproxScale]
        positivity))
      (((tendsto_order.1 tendsto_unitConvexApproxScale_zero).2 1 zero_lt_one).mono
        (fun _ hn => hn)))


end Homogenization
