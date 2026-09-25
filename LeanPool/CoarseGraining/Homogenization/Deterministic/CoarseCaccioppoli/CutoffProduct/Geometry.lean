/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfacesComponentwise
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoliLocalBridge
public import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMetric
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareLpSmooth
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! # Geometry -/

@[expose] public section

namespace Homogenization

noncomputable section

open MeasureTheory.Measure
open scoped BigOperators ENNReal

theorem cubeScaleFactor_nonneg {d : ℕ} (Q : TriadicCube d) :
    0 ≤ cubeScaleFactor Q := by
  simpa [cubeScaleFactor] using
    (le_of_lt (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale))

theorem cubeLpNorm_infty_le_of_bound_on_cubeSet {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (Q : TriadicCube d) (f : Vec d → E) {C : ℝ}
    (hC : 0 ≤ C)
    (hbound : ∀ x ∈ cubeSet Q, ‖f x‖ ≤ C) :
    cubeLpNorm Q ∞ f ≤ C := by
  have hbound_ae_cube : ∀ᵐ x ∂ cubeMeasure Q, ‖f x‖ ≤ C := by
    exact (MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)).2 <|
      Filter.Eventually.of_forall hbound
  have hbound_ae : ∀ᵐ x ∂ normalizedCubeMeasure Q, ‖f x‖ ≤ C := by
    simpa [normalizedCubeMeasure] using
      (ae_smul_measure hbound_ae_cube (ENNReal.ofReal ((cubeVolume Q)⁻¹)))
  have hle :
      MeasureTheory.eLpNorm f ∞ (normalizedCubeMeasure Q) ≤ ENNReal.ofReal C := by
    simpa [MeasureTheory.eLpNorm_exponent_top] using
      MeasureTheory.eLpNormEssSup_le_of_ae_bound hbound_ae
  have htoReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  simpa [cubeLpNorm, ENNReal.toReal_ofReal, hC] using htoReal

theorem convex_cubeSet {d : ℕ} (Q : TriadicCube d) :
    Convex ℝ (cubeSet Q) := by
  rw [cubeSet_eq_pi_Ico]
  refine convex_pi ?_
  intro i hi
  exact convex_Ico _ _

theorem norm_sub_le_cubeScaleFactor_of_mem_cubeSet {d : ℕ} (Q : TriadicCube d)
    {x y : Vec d} (hx : x ∈ cubeSet Q) (hy : y ∈ cubeSet Q) :
    ‖x - y‖ ≤ cubeScaleFactor Q := by
  have hxball : x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q) :=
    cubeSet_subset_closedBall Q hx
  have hyball : y ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q) :=
    cubeSet_subset_closedBall Q hy
  have hxnorm : ‖x - cubeCenter Q‖ ≤ cubeRadius Q := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hxball
  have hynorm : ‖y - cubeCenter Q‖ ≤ cubeRadius Q := by
    simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hyball
  have hycnorm : ‖cubeCenter Q - y‖ ≤ cubeRadius Q := by
    simpa [norm_sub_rev] using hynorm
  calc
    ‖x - y‖ = ‖(x - cubeCenter Q) + (cubeCenter Q - y)‖ := by
      congr
      abel_nf
    _ ≤ ‖x - cubeCenter Q‖ + ‖cubeCenter Q - y‖ := norm_add_le _ _
    _ ≤ cubeRadius Q + cubeRadius Q := add_le_add hxnorm hycnorm
    _ = cubeScaleFactor Q := by
      unfold cubeRadius
      ring

theorem norm_sub_le_cubeScaleFactor_mul_of_contDiff_bound {d : ℕ} (Q : TriadicCube d)
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) {B : ℝ} (hB : 0 ≤ B)
    (hderiv : ∀ z ∈ cubeSet Q, ‖fderiv ℝ u z‖ ≤ B)
    {x y : Vec d} (hx : x ∈ cubeSet Q) (hy : y ∈ cubeSet Q) :
    ‖u x - u y‖ ≤ cubeScaleFactor Q * B := by
  let γ : ℝ → Vec d := fun t => segmentBlend x t y
  have hγ_cont : Continuous γ := by
    simpa [γ, segmentBlend] using (AffineMap.lineMap_continuous (p := y) (q := x))
  have hfderiv_cont : Continuous (fderiv ℝ u) := by
    exact hu.continuous_fderiv (by simp)
  have hint :
      IntervalIntegrable (fun t => ‖fderiv ℝ u (γ t)‖ * ‖x - y‖)
        MeasureTheory.volume 0 1 := by
    have hcont : Continuous (fun t => ‖fderiv ℝ u (γ t)‖ * ‖x - y‖) :=
      (continuous_norm.comp (hfderiv_cont.comp hγ_cont)).mul continuous_const
    exact hcont.intervalIntegrable _ _
  have hconst_int :
      IntervalIntegrable (fun _ : ℝ => B * ‖x - y‖) MeasureTheory.volume 0 1 :=
    intervalIntegrable_const
  have hpoint :
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ u (γ t)‖ * ‖x - y‖ ≤ B * ‖x - y‖ := by
    intro t ht
    have hγ_mem : γ t ∈ cubeSet Q := by
      exact segmentBlend_mem (convex_cubeSet Q) hx hy ht.1 ht.2
    exact mul_le_mul_of_nonneg_right (hderiv (γ t) hγ_mem) (norm_nonneg _)
  have hdist : ‖x - y‖ ≤ cubeScaleFactor Q :=
    norm_sub_le_cubeScaleFactor_of_mem_cubeSet Q hx hy
  calc
    ‖u x - u y‖
        ≤ ∫ t in (0 : ℝ)..1, ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ := by
            simpa [γ] using
              norm_sub_le_integral_norm_fderiv_mul_norm_sub_along_segment hu x y
    _ ≤ ∫ t in (0 : ℝ)..1, B * ‖x - y‖ := by
          exact intervalIntegral.integral_mono_on zero_le_one hint hconst_int hpoint
    _ = B * ‖x - y‖ := by simp
    _ ≤ B * cubeScaleFactor Q := by
          exact mul_le_mul_of_nonneg_left hdist hB
    _ = cubeScaleFactor Q * B := by ring

theorem norm_sub_le_cubeScaleFactor_mul_of_contDiff_component_bound {d : ℕ}
    (Q : TriadicCube d) {ξ : Vec d → Vec d} {B : ℝ} (hB : 0 ≤ B)
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    {x y : Vec d} (hx : x ∈ cubeSet Q) (hy : y ∈ cubeSet Q) :
    ‖ξ x - ξ y‖ ≤ cubeScaleFactor Q * B := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (cubeScaleFactor_nonneg Q) hB)).2 ?_
  intro i
  simpa using
    norm_sub_le_cubeScaleFactor_mul_of_contDiff_bound Q (u := fun z => ξ z i) (hξ i) hB
      (fun z hz => hderiv i z hz) hx hy

theorem cubeLpNorm_component_le_cubeLpNorm {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞)
    (u : Vec d → Vec d) (i : Fin d)
    (hu : MeasureTheory.MemLp u p (normalizedCubeMeasure Q)) :
    cubeLpNorm Q p (fun x => u x i) ≤ cubeLpNorm Q p u := by
  have hui : MeasureTheory.MemLp (fun x => u x i) p (normalizedCubeMeasure Q) := by
    simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hu
  have hpoint :
      ∀ᵐ x ∂ normalizedCubeMeasure Q, ‖u x i‖ ≤ (1 : ℝ) * ‖u x‖ := by
    exact Filter.Eventually.of_forall fun x => by
      simpa using (norm_le_pi_norm (u x) i)
  have hle :
      MeasureTheory.eLpNorm (fun x => u x i) p (normalizedCubeMeasure Q) ≤
        ENNReal.ofReal (1 : ℝ) *
          MeasureTheory.eLpNorm u p (normalizedCubeMeasure Q) :=
    MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpoint p
  have htop_u :
      MeasureTheory.eLpNorm u p (normalizedCubeMeasure Q) ≠ ∞ := ne_of_lt hu.2
  have htop_ui :
      MeasureTheory.eLpNorm (fun x => u x i) p (normalizedCubeMeasure Q) ≠ ∞ :=
    ne_of_lt hui.2
  have htoReal :
      (MeasureTheory.eLpNorm (fun x => u x i) p (normalizedCubeMeasure Q)).toReal ≤
        (MeasureTheory.eLpNorm u p (normalizedCubeMeasure Q)).toReal := by
    have hle' :
        MeasureTheory.eLpNorm (fun x => u x i) p (normalizedCubeMeasure Q) ≤
          MeasureTheory.eLpNorm u p (normalizedCubeMeasure Q) := by
      simpa using hle
    exact ENNReal.toReal_mono htop_u hle'
  simpa [cubeLpNorm] using htoReal

theorem norm_cubeAverageVec_le_cubeLpNorm_two {d : ℕ} (Q : TriadicCube d)
    (u : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ‖cubeAverageVec Q u‖ ≤ cubeLpNorm Q (2 : ℝ≥0∞) u := by
  have hconj_two : ENNReal.conjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  refine (pi_norm_le_iff_of_nonneg (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) u)).2 ?_
  intro i
  have hui : MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hu
  have hconst : MeasureTheory.MemLp (fun _ : Vec d => (1 : ℝ))
      (ENNReal.conjExponent (2 : ℝ≥0∞)) (normalizedCubeMeasure Q) := by
    simpa [hconj_two] using
      (MeasureTheory.memLp_const (1 : ℝ) :
        MeasureTheory.MemLp (fun _ : Vec d => (1 : ℝ))
          (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
  have havg :
      ‖cubeAverage Q (fun x => u x i)‖ ≤
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u x i) *
          cubeLpNorm Q (2 : ℝ≥0∞) (fun _ => (1 : ℝ)) := by
    simpa [hconj_two] using
      abs_cubeAverage_mul_le_mul_cubeLpNorm_conjExponent
        (Q := Q) (p := (2 : ℝ≥0∞)) (f := fun x => u x i) (g := fun _ => (1 : ℝ))
        hui hconst (by norm_num)
  have hnorm_one : cubeLpNorm Q (2 : ℝ≥0∞) (fun _ => (1 : ℝ)) = 1 := by
    simpa using cubeLpNorm_const (Q := Q) (p := (2 : ℝ≥0∞)) (c := (1 : ℝ)) (by norm_num)
  have havg' :
      ‖cubeAverage Q (fun x => u x i)‖ ≤ cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u x i) := by
    simpa [hnorm_one] using havg
  calc
    ‖cubeAverageVec Q u i‖ = ‖cubeAverage Q (fun x => u x i)‖ := by
      simp [cubeAverageVec]
    _ ≤ cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u x i) := havg'
    _ ≤ cubeLpNorm Q (2 : ℝ≥0∞) u :=
      cubeLpNorm_component_le_cubeLpNorm Q (2 : ℝ≥0∞) u i hu

theorem norm_cubeAverageVec_le_cubeLpNorm_infty {d : ℕ} (Q : TriadicCube d)
    (u : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u ∞ (normalizedCubeMeasure Q)) :
    ‖cubeAverageVec Q u‖ ≤ cubeLpNorm Q ∞ u := by
  have hconj_top : ENNReal.conjExponent (∞ : ℝ≥0∞) = (1 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (∞ : ℝ≥0∞)) (q := (1 : ℝ≥0∞)))
  refine (pi_norm_le_iff_of_nonneg (cubeLpNorm_nonneg Q ∞ u)).2 ?_
  intro i
  have hui : MeasureTheory.MemLp (fun x => u x i) ∞ (normalizedCubeMeasure Q) := by
    simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hu
  have hconst : MeasureTheory.MemLp (fun _ : Vec d => (1 : ℝ))
      (ENNReal.conjExponent (∞ : ℝ≥0∞)) (normalizedCubeMeasure Q) := by
    simpa [hconj_top] using
      (MeasureTheory.memLp_const (1 : ℝ) :
        MeasureTheory.MemLp (fun _ : Vec d => (1 : ℝ))
          (1 : ℝ≥0∞) (normalizedCubeMeasure Q))
  have havg :
      ‖cubeAverage Q (fun x => u x i)‖ ≤
        cubeLpNorm Q ∞ (fun x => u x i) * cubeLpNorm Q (1 : ℝ≥0∞) (fun _ => (1 : ℝ)) := by
    simpa [hconj_top] using
      abs_cubeAverage_mul_le_mul_cubeLpNorm_conjExponent
        (Q := Q) (p := (∞ : ℝ≥0∞)) (f := fun x => u x i) (g := fun _ => (1 : ℝ))
        hui hconst (by norm_num)
  have hnorm_one : cubeLpNorm Q (1 : ℝ≥0∞) (fun _ => (1 : ℝ)) = 1 := by
    simpa using cubeLpNorm_const (Q := Q) (p := (1 : ℝ≥0∞)) (c := (1 : ℝ)) (by norm_num)
  have havg' :
      ‖cubeAverage Q (fun x => u x i)‖ ≤ cubeLpNorm Q ∞ (fun x => u x i) := by
    simpa [hnorm_one] using havg
  calc
    ‖cubeAverageVec Q u i‖ = ‖cubeAverage Q (fun x => u x i)‖ := by
      simp [cubeAverageVec]
    _ ≤ cubeLpNorm Q ∞ (fun x => u x i) := havg'
    _ ≤ cubeLpNorm Q ∞ u :=
      cubeLpNorm_component_le_cubeLpNorm Q ∞ u i hu

theorem cubeAverage_sub_const {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) (c : ℝ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x => u x - c) = cubeAverage Q u - c := by
  have hu_int : MeasureTheory.Integrable u (normalizedCubeMeasure Q) :=
    hu.integrable (by norm_num)
  have hc_int : MeasureTheory.Integrable (fun _ : Vec d => c) (normalizedCubeMeasure Q) :=
    MeasureTheory.integrable_const _
  calc
    cubeAverage Q (fun x => u x - c)
        = ∫ x, (u x - c) ∂ normalizedCubeMeasure Q := by
            rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    _ = ∫ x, u x ∂ normalizedCubeMeasure Q - ∫ x, c ∂ normalizedCubeMeasure Q := by
          rw [MeasureTheory.integral_sub hu_int hc_int]
    _ = cubeAverage Q u - cubeAverage Q (fun _ => c) := by
          rw [cubeAverage_eq_integral_normalizedCubeMeasure,
            cubeAverage_eq_integral_normalizedCubeMeasure]
    _ = cubeAverage Q u - c := by rw [cubeAverage_const]

@[simp] theorem cubeFluctuation_sub_const {d : ℕ} (Q : TriadicCube d)
    (u : Vec d → ℝ) (c : ℝ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeFluctuation Q (fun x => u x - c) = cubeFluctuation Q u := by
  funext x
  simp [cubeFluctuation, cubeAverage_sub_const, hu]

theorem norm_sub_cubeAverageVec_le_cubeLpNorm_infty_sub_const {d : ℕ}
    (Q : TriadicCube d) (ξ : Vec d → Vec d) (x : Vec d)
    (hξ : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q)) :
    ‖ξ x - cubeAverageVec Q ξ‖ ≤ cubeLpNorm Q ∞ (fun y => ξ y - ξ x) := by
  have hξ_sub :
      MeasureTheory.MemLp (fun y => ξ y - ξ x) ∞ (normalizedCubeMeasure Q) :=
    hξ.sub (MeasureTheory.memLp_const (ξ x))
  have hξ_two : MeasureTheory.MemLp ξ (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    hξ.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ ∞)
  calc
    ‖ξ x - cubeAverageVec Q ξ‖ = ‖cubeAverageVec Q ξ - ξ x‖ := by
      simpa using (norm_sub_rev (ξ x) (cubeAverageVec Q ξ))
    _ = ‖cubeAverageVec Q (fun y => ξ y - ξ x)‖ := by
      rw [cubeAverageVec_sub_const Q ξ (ξ x) hξ_two]
    _ ≤ cubeLpNorm Q ∞ (fun y => ξ y - ξ x) :=
      norm_cubeAverageVec_le_cubeLpNorm_infty Q (fun y => ξ y - ξ x) hξ_sub

theorem norm_sub_cubeAverageVec_le_cubeScaleFactor_mul_of_contDiff_component_bound {d : ℕ}
    (Q : TriadicCube d) {ξ : Vec d → Vec d} {B : ℝ} (hB : 0 ≤ B)
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    {x : Vec d} (hx : x ∈ cubeSet Q) :
    ‖ξ x - cubeAverageVec Q ξ‖ ≤ cubeScaleFactor Q * B := by
  have havg :
      ‖ξ x - cubeAverageVec Q ξ‖ ≤ cubeLpNorm Q ∞ (fun y => ξ y - ξ x) :=
    norm_sub_cubeAverageVec_le_cubeLpNorm_infty_sub_const Q ξ x hξLp
  have hlinfty :
      cubeLpNorm Q ∞ (fun y => ξ y - ξ x) ≤ cubeScaleFactor Q * B := by
    apply cubeLpNorm_infty_le_of_bound_on_cubeSet Q (hC := mul_nonneg (cubeScaleFactor_nonneg Q) hB)
    intro y hy
    simpa [norm_sub_rev] using
      norm_sub_le_cubeScaleFactor_mul_of_contDiff_component_bound
        Q hB hξ hderiv hy hx
  exact le_trans havg hlinfty

theorem cubeLpNorm_infty_sub_cubeAverageVec_le_cubeScaleFactor_mul_of_contDiff_component_bound
    {d : ℕ} (Q : TriadicCube d) {ξ : Vec d → Vec d} {B : ℝ} (hB : 0 ≤ B)
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B) :
    cubeLpNorm Q ∞ (fun x => ξ x - cubeAverageVec Q ξ) ≤ cubeScaleFactor Q * B := by
  apply cubeLpNorm_infty_le_of_bound_on_cubeSet Q (hC := mul_nonneg (cubeScaleFactor_nonneg Q) hB)
  intro x hx
  exact norm_sub_cubeAverageVec_le_cubeScaleFactor_mul_of_contDiff_component_bound
    Q hB hξLp hξ hderiv hx

theorem norm_cubeAverage_le_cubeLpNorm_infty {d : ℕ} (Q : TriadicCube d)
    (u : Vec d → ℝ)
    (hu : MeasureTheory.MemLp u ∞ (normalizedCubeMeasure Q)) :
    ‖cubeAverage Q u‖ ≤ cubeLpNorm Q ∞ u := by
  have hconj_top : ENNReal.conjExponent (∞ : ℝ≥0∞) = (1 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (∞ : ℝ≥0∞)) (q := (1 : ℝ≥0∞)))
  have hconst : MeasureTheory.MemLp (fun _ : Vec d => (1 : ℝ))
      (ENNReal.conjExponent (∞ : ℝ≥0∞)) (normalizedCubeMeasure Q) := by
    simpa [hconj_top] using
      (MeasureTheory.memLp_const (1 : ℝ) :
        MeasureTheory.MemLp (fun _ : Vec d => (1 : ℝ))
          (1 : ℝ≥0∞) (normalizedCubeMeasure Q))
  have havg :
      ‖cubeAverage Q u‖ ≤
        cubeLpNorm Q ∞ u * cubeLpNorm Q (1 : ℝ≥0∞) (fun _ => (1 : ℝ)) := by
    simpa [hconj_top] using
      abs_cubeAverage_mul_le_mul_cubeLpNorm_conjExponent
        (Q := Q) (p := (∞ : ℝ≥0∞)) (f := u) (g := fun _ => (1 : ℝ))
        hu hconst (by norm_num)
  have hnorm_one : cubeLpNorm Q (1 : ℝ≥0∞) (fun _ => (1 : ℝ)) = 1 := by
    simpa using cubeLpNorm_const (Q := Q) (p := (1 : ℝ≥0∞)) (c := (1 : ℝ)) (by norm_num)
  simpa [hnorm_one] using havg

theorem norm_cubeAverage_le_cubeLpNorm_two {d : ℕ} (Q : TriadicCube d)
    (u : Vec d → ℝ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ‖cubeAverage Q u‖ ≤ cubeLpNorm Q (2 : ℝ≥0∞) u := by
  have hconj_two : ENNReal.conjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hconst : MeasureTheory.MemLp (fun _ : Vec d => (1 : ℝ))
      (ENNReal.conjExponent (2 : ℝ≥0∞)) (normalizedCubeMeasure Q) := by
    simpa [hconj_two] using
      (MeasureTheory.memLp_const (1 : ℝ) :
        MeasureTheory.MemLp (fun _ : Vec d => (1 : ℝ))
          (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
  have havg :
      ‖cubeAverage Q u‖ ≤
        cubeLpNorm Q (2 : ℝ≥0∞) u * cubeLpNorm Q (2 : ℝ≥0∞) (fun _ => (1 : ℝ)) := by
    simpa [hconj_two] using
      abs_cubeAverage_mul_le_mul_cubeLpNorm_conjExponent
        (Q := Q) (p := (2 : ℝ≥0∞)) (f := u) (g := fun _ => (1 : ℝ))
        hu hconst (by norm_num)
  have hnorm_one : cubeLpNorm Q (2 : ℝ≥0∞) (fun _ => (1 : ℝ)) = 1 := by
    simpa using cubeLpNorm_const (Q := Q) (p := (2 : ℝ≥0∞)) (c := (1 : ℝ)) (by norm_num)
  simpa [hnorm_one] using havg

theorem norm_sub_cubeAverage_le_cubeLpNorm_infty_sub_const {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → ℝ) (x : Vec d)
    (hu : MeasureTheory.MemLp u ∞ (normalizedCubeMeasure Q)) :
    ‖u x - cubeAverage Q u‖ ≤ cubeLpNorm Q ∞ (fun y => u y - u x) := by
  have hu_sub :
      MeasureTheory.MemLp (fun y => u y - u x) ∞ (normalizedCubeMeasure Q) :=
    hu.sub (MeasureTheory.memLp_const (u x))
  have hu_two : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    hu.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ ∞)
  calc
    ‖u x - cubeAverage Q u‖ = ‖cubeAverage Q u - u x‖ := by
      simpa using (norm_sub_rev (u x) (cubeAverage Q u))
    _ = ‖cubeAverage Q (fun y => u y - u x)‖ := by
          rw [cubeAverage_sub_const Q u (u x) hu_two]
    _ ≤ cubeLpNorm Q ∞ (fun y => u y - u x) :=
          norm_cubeAverage_le_cubeLpNorm_infty Q (fun y => u y - u x) hu_sub

theorem cubeLpNorm_infty_sub_cubeAverage_le_cubeScaleFactor_mul_of_contDiff_bound
    {d : ℕ} (Q : TriadicCube d) {u : Vec d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (huLp : MeasureTheory.MemLp u ∞ (normalizedCubeMeasure Q))
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hderiv : ∀ z ∈ cubeSet Q, ‖fderiv ℝ u z‖ ≤ B) :
    cubeLpNorm Q ∞ (fun x => u x - cubeAverage Q u) ≤ cubeScaleFactor Q * B := by
  apply cubeLpNorm_infty_le_of_bound_on_cubeSet Q (hC := mul_nonneg (cubeScaleFactor_nonneg Q) hB)
  intro x hx
  have havg :
      ‖u x - cubeAverage Q u‖ ≤ cubeLpNorm Q ∞ (fun y => u y - u x) :=
    norm_sub_cubeAverage_le_cubeLpNorm_infty_sub_const Q u x huLp
  have hlinfty :
      cubeLpNorm Q ∞ (fun y => u y - u x) ≤ cubeScaleFactor Q * B := by
    apply cubeLpNorm_infty_le_of_bound_on_cubeSet Q (hC := mul_nonneg (cubeScaleFactor_nonneg Q) hB)
    intro y hy
    simpa [norm_sub_rev] using
      norm_sub_le_cubeScaleFactor_mul_of_contDiff_bound Q hu hB
        (fun z hz => hderiv z hz) hy hx
  exact le_trans havg hlinfty

theorem cubeLpNorm_two_le_cubeLpNorm_infty_of_memLp_infty {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → ℝ)
    (hu : MeasureTheory.MemLp u ∞ (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) u ≤ cubeLpNorm Q ∞ u := by
  let : MeasureTheory.IsProbabilityMeasure (normalizedCubeMeasure Q) := by
    refine ⟨?_⟩
    simp [normalizedCubeMeasure_apply_univ Q]
  have hle :
      MeasureTheory.eLpNorm u (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ≤
        MeasureTheory.eLpNorm u ∞ (normalizedCubeMeasure Q) := by
    exact MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hu.1
  have htoReal := ENNReal.toReal_mono (ne_of_lt hu.2) hle
  simpa [cubeLpNorm] using htoReal

theorem cubeBesovOscillation_two_le_cubeScaleFactor_mul_of_contDiff_bound {d : ℕ}
    (Q : TriadicCube d) {u : Vec d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (huLp : MeasureTheory.MemLp u ∞ (normalizedCubeMeasure Q))
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hderiv : ∀ z ∈ cubeSet Q, ‖fderiv ℝ u z‖ ≤ B) :
    cubeBesovOscillation Q (2 : ℝ≥0∞) u ≤ cubeScaleFactor Q * B := by
  have hfluctLp :
      MeasureTheory.MemLp (fun x => u x - cubeAverage Q u) ∞ (normalizedCubeMeasure Q) :=
    huLp.sub (MeasureTheory.memLp_const (cubeAverage Q u))
  calc
    cubeBesovOscillation Q (2 : ℝ≥0∞) u
        = cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u x - cubeAverage Q u) := by
            rfl
    _ ≤ cubeLpNorm Q ∞ (fun x => u x - cubeAverage Q u) := by
          exact cubeLpNorm_two_le_cubeLpNorm_infty_of_memLp_infty Q
            (fun x => u x - cubeAverage Q u) hfluctLp
    _ ≤ cubeScaleFactor Q * B := by
          exact cubeLpNorm_infty_sub_cubeAverage_le_cubeScaleFactor_mul_of_contDiff_bound
            Q hB huLp hu hderiv

theorem cubeBesovDepthSeminorm_one_two_le_of_contDiff_bound {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → ℝ) (j : ℕ) {B : ℝ}
    (hB : 0 ≤ B)
    (huLp : MeasureTheory.MemLp u ∞ (normalizedCubeMeasure Q))
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hderiv : ∀ z ∈ cubeSet Q, ‖fderiv ℝ u z‖ ≤ B) :
    cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) u j ≤ B := by
  let A : ℝ := cubeScaleFactor Q / (3 : ℝ) ^ j
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (cubeScaleFactor_nonneg Q) (by positivity)
  have hA_pos : 0 < A := by
    dsimp [A]
    exact div_pos
      (by simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale))
      (by positivity)
  have hbound :
      cubeBesovDepthAverage Q (2 : ℝ≥0∞) u j ≤ (A * B) ^ (2 : ℝ) := by
    unfold cubeBesovDepthAverage
    calc
      descendantsAverage Q j (fun R => cubeBesovOscillation R (2 : ℝ≥0∞) u ^ ENNReal.toReal 2)
          ≤ descendantsAverage Q j (fun _ : TriadicCube d => (A * B) ^ (2 : ℝ)) := by
              refine descendantsAverage_le_descendantsAverage Q j ?_
              intro R hR
              have huR : MeasureTheory.MemLp u ∞ (normalizedCubeMeasure R) :=
                memLp_on_descendant_of_memLp_generic (E := ℝ) hR huLp
              have hosc :
                  cubeBesovOscillation R (2 : ℝ≥0∞) u ≤ cubeScaleFactor R * B := by
                exact cubeBesovOscillation_two_le_cubeScaleFactor_mul_of_contDiff_bound
                  R hB huR hu (fun z hz => hderiv z (cubeSet_subset_of_mem_descendantsAtDepth hR hz))
              have hRB_eq : cubeScaleFactor R * B = A * B := by
                rw [cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth hR]
              have hosc_nonneg : 0 ≤ cubeBesovOscillation R (2 : ℝ≥0∞) u :=
                cubeBesovOscillation_nonneg R (2 : ℝ≥0∞) u
              have hAB_nonneg : 0 ≤ A * B := mul_nonneg hA_nonneg hB
              have hsq :
                  (cubeBesovOscillation R (2 : ℝ≥0∞) u) ^ (2 : ℝ) ≤ (A * B) ^ (2 : ℝ) := by
                rw [← hRB_eq]
                exact Real.rpow_le_rpow hosc_nonneg hosc (by norm_num)
              simpa using hsq
      _ = (A * B) ^ (2 : ℝ) := by
            simp [descendantsAverage_const]
  have hsqrt :
      Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) u j) ≤ A * B := by
    have hAB_nonneg : 0 ≤ A * B := mul_nonneg hA_nonneg hB
    calc
      Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) u j)
          ≤ Real.sqrt ((A * B) ^ (2 : ℝ)) := by
              exact Real.sqrt_le_sqrt hbound
      _ = A * B := by
            rw [show (A * B) ^ (2 : ℝ) = (A * B) ^ (2 : ℕ) by norm_num]
            rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hAB_nonneg]
  have hweight_nonneg : 0 ≤ cubeBesovDepthWeight Q 1 j :=
    cubeBesovDepthWeight_nonneg Q 1 j
  calc
    cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) u j
        = cubeBesovDepthWeight Q 1 j * Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) u j) := by
            simp [cubeBesovDepthSeminorm, Real.sqrt_eq_rpow]
    _ ≤ cubeBesovDepthWeight Q 1 j * (A * B) := by
          exact mul_le_mul_of_nonneg_left hsqrt hweight_nonneg
    _ = B := by
          dsimp [A]
          have hinv :
              (cubeScaleFactor Q / (3 : ℝ) ^ j) ^ (-1 : ℝ) *
                  ((cubeScaleFactor Q / (3 : ℝ) ^ j) * B) =
                B := by
            calc
              (cubeScaleFactor Q / (3 : ℝ) ^ j) ^ (-1 : ℝ) *
                  ((cubeScaleFactor Q / (3 : ℝ) ^ j) * B)
                  =
                ((cubeScaleFactor Q / (3 : ℝ) ^ j) ^ (-1 : ℝ) *
                    (cubeScaleFactor Q / (3 : ℝ) ^ j)) * B := by
                      ring
              _ = B := by
                    rw [Real.rpow_neg_one, inv_mul_cancel₀ hA_pos.ne', one_mul]
          simpa [cubeBesovDepthWeight] using hinv

theorem cubeBesovPartialSeminormTop_one_two_le_of_contDiff_bound {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → ℝ) (N : ℕ) {B : ℝ}
    (hB : 0 ≤ B)
    (huLp : MeasureTheory.MemLp u ∞ (normalizedCubeMeasure Q))
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hderiv : ∀ z ∈ cubeSet Q, ‖fderiv ℝ u z‖ ≤ B) :
    cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) N u ≤ B := by
  classical
  unfold cubeBesovPartialSeminormTop
  refine Finset.sup'_le
    (s := Finset.range (N + 1))
    (H := ⟨0, by simp⟩)
    (f := fun j : ℕ => cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) u j) ?_
  intro j hj
  exact cubeBesovDepthSeminorm_one_two_le_of_contDiff_bound Q u j hB huLp hu hderiv

theorem cubeBesovPartialNormTop_one_two_le_of_contDiff_bound {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → ℝ) (N : ℕ) {B : ℝ}
    (hB : 0 ≤ B)
    (huLp : MeasureTheory.MemLp u ∞ (normalizedCubeMeasure Q))
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hderiv : ∀ z ∈ cubeSet Q, ‖fderiv ℝ u z‖ ≤ B) :
    cubeBesovPartialNormTop Q 1 (2 : ℝ≥0∞) N u ≤
      B + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ u := by
  unfold cubeBesovPartialNormTop
  exact add_le_add
    (cubeBesovPartialSeminormTop_one_two_le_of_contDiff_bound Q u N hB huLp hu hderiv)
    (mul_le_mul_of_nonneg_left
      (norm_cubeAverage_le_cubeLpNorm_infty Q u huLp)
      (cubeBesovScaleWeight_nonneg 1 Q))

theorem cubeBesovDualTestNorm_one_two_le_of_contDiff_bound {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → ℝ) (N : ℕ) {B : ℝ}
    (hB : 0 ≤ B)
    (huLp : MeasureTheory.MemLp u ∞ (normalizedCubeMeasure Q))
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hderiv : ∀ z ∈ cubeSet Q, ‖fderiv ℝ u z‖ ≤ B) :
    cubeBesovDualTestNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N u ≤
      B + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ u := by
  have hq : cubeBesovConjExponent (1 : ℝ≥0∞) = ∞ := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (1 : ℝ≥0∞)) (q := (∞ : ℝ≥0∞)))
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  rw [cubeBesovDualTestNorm_of_conjExponent_eq_top Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N u hq]
  rw [hpConj]
  exact cubeBesovPartialNormTop_one_two_le_of_contDiff_bound Q u N hB huLp hu hderiv

theorem cubeBesovDepthSeminorm_two_le_scaleWeight_mul_scaleFactor_mul_of_contDiff_bound_of_le_one
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) (j : ℕ) {s B : ℝ}
    (hs1 : s ≤ 1) (hB : 0 ≤ B)
    (huLp : MeasureTheory.MemLp u ∞ (normalizedCubeMeasure Q))
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hderiv : ∀ z ∈ cubeSet Q, ‖fderiv ℝ u z‖ ≤ B) :
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j ≤
      cubeBesovScaleWeight s Q * cubeScaleFactor Q * B := by
  let A : ℝ := cubeScaleFactor Q / (3 : ℝ) ^ j
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (cubeScaleFactor_nonneg Q) (by positivity)
  have hA_pos : 0 < A := by
    dsimp [A]
    exact div_pos
      (by simpa [cubeScaleFactor] using
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale))
      (by positivity)
  have hbound :
      cubeBesovDepthAverage Q (2 : ℝ≥0∞) u j ≤ (A * B) ^ (2 : ℝ) := by
    unfold cubeBesovDepthAverage
    calc
      descendantsAverage Q j
          (fun R => cubeBesovOscillation R (2 : ℝ≥0∞) u ^ ENNReal.toReal 2)
          ≤ descendantsAverage Q j (fun _ : TriadicCube d => (A * B) ^ (2 : ℝ)) := by
              refine descendantsAverage_le_descendantsAverage Q j ?_
              intro R hR
              have huR : MeasureTheory.MemLp u ∞ (normalizedCubeMeasure R) :=
                memLp_on_descendant_of_memLp_generic (E := ℝ) hR huLp
              have hosc :
                  cubeBesovOscillation R (2 : ℝ≥0∞) u ≤ cubeScaleFactor R * B := by
                exact cubeBesovOscillation_two_le_cubeScaleFactor_mul_of_contDiff_bound
                  R hB huR hu
                  (fun z hz => hderiv z (cubeSet_subset_of_mem_descendantsAtDepth hR hz))
              have hRB_eq : cubeScaleFactor R * B = A * B := by
                rw [cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth hR]
              have hosc_nonneg : 0 ≤ cubeBesovOscillation R (2 : ℝ≥0∞) u :=
                cubeBesovOscillation_nonneg R (2 : ℝ≥0∞) u
              have hsq :
                  (cubeBesovOscillation R (2 : ℝ≥0∞) u) ^ (2 : ℝ) ≤
                    (A * B) ^ (2 : ℝ) := by
                rw [← hRB_eq]
                exact Real.rpow_le_rpow hosc_nonneg hosc (by norm_num)
              simpa using hsq
      _ = (A * B) ^ (2 : ℝ) := by
            simp [descendantsAverage_const]
  have hsqrt :
      Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) u j) ≤ A * B := by
    have hAB_nonneg : 0 ≤ A * B := mul_nonneg hA_nonneg hB
    calc
      Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) u j)
          ≤ Real.sqrt ((A * B) ^ (2 : ℝ)) := by
              exact Real.sqrt_le_sqrt hbound
      _ = A * B := by
            rw [show (A * B) ^ (2 : ℝ) = (A * B) ^ (2 : ℕ) by norm_num]
            rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hAB_nonneg]
  have hweight_nonneg : 0 ≤ cubeBesovDepthWeight Q s j :=
    cubeBesovDepthWeight_nonneg Q s j
  have hA_le_scale : A ≤ cubeScaleFactor Q := by
    dsimp [A]
    have hden : (1 : ℝ) ≤ (3 : ℝ) ^ j :=
      one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
    have hscale_nonneg : 0 ≤ cubeScaleFactor Q := cubeScaleFactor_nonneg Q
    calc
      cubeScaleFactor Q / (3 : ℝ) ^ j ≤ cubeScaleFactor Q / 1 := by
        exact div_le_div_of_nonneg_left hscale_nonneg (by positivity) hden
      _ = cubeScaleFactor Q := by ring
  have hpow_le : A ^ (1 - s) ≤ (cubeScaleFactor Q) ^ (1 - s) := by
    exact Real.rpow_le_rpow hA_nonneg hA_le_scale (sub_nonneg.mpr hs1)
  have hweightA : cubeBesovDepthWeight Q s j * A = A ^ (1 - s) := by
    dsimp [cubeBesovDepthWeight, A]
    calc
      A ^ (-s) * A = A ^ (-s) * A ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = A ^ ((-s) + 1) := by rw [← Real.rpow_add hA_pos]
      _ = A ^ (1 - s) := by ring_nf
  have hscale_pos : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hscale_eq :
      cubeBesovScaleWeight s Q * cubeScaleFactor Q =
        (cubeScaleFactor Q) ^ (1 - s) := by
    unfold cubeBesovScaleWeight
    calc
      (cubeScaleFactor Q) ^ (-s) * cubeScaleFactor Q =
          (cubeScaleFactor Q) ^ (-s) * (cubeScaleFactor Q) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
      _ = (cubeScaleFactor Q) ^ ((-s) + 1) := by rw [← Real.rpow_add hscale_pos]
      _ = (cubeScaleFactor Q) ^ (1 - s) := by ring_nf
  calc
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j
        = cubeBesovDepthWeight Q s j *
            Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) u j) := by
            simp [cubeBesovDepthSeminorm, Real.sqrt_eq_rpow]
    _ ≤ cubeBesovDepthWeight Q s j * (A * B) := by
          exact mul_le_mul_of_nonneg_left hsqrt hweight_nonneg
    _ = (cubeBesovDepthWeight Q s j * A) * B := by ring
    _ = A ^ (1 - s) * B := by rw [hweightA]
    _ ≤ (cubeScaleFactor Q) ^ (1 - s) * B := by
          exact mul_le_mul_of_nonneg_right hpow_le hB
    _ = cubeBesovScaleWeight s Q * cubeScaleFactor Q * B := by rw [← hscale_eq]

theorem cubeBesovPartialSeminormTop_two_le_scaleWeight_mul_scaleFactor_mul_of_contDiff_bound_of_le_one
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) (N : ℕ) {s B : ℝ}
    (hs1 : s ≤ 1) (hB : 0 ≤ B)
    (huLp : MeasureTheory.MemLp u ∞ (normalizedCubeMeasure Q))
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hderiv : ∀ z ∈ cubeSet Q, ‖fderiv ℝ u z‖ ≤ B) :
    cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) N u ≤
      cubeBesovScaleWeight s Q * cubeScaleFactor Q * B := by
  classical
  unfold cubeBesovPartialSeminormTop
  refine Finset.sup'_le
    (s := Finset.range (N + 1))
    (H := ⟨0, by simp⟩)
    (f := fun j : ℕ => cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ?_
  intro j hj
  exact
    cubeBesovDepthSeminorm_two_le_scaleWeight_mul_scaleFactor_mul_of_contDiff_bound_of_le_one
      Q u j hs1 hB huLp hu hderiv

theorem cubeBesovPartialNormTop_two_le_scaleWeight_mul_of_contDiff_bound_of_le_one
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) (N : ℕ) {s B : ℝ}
    (hs1 : s ≤ 1) (hB : 0 ≤ B)
    (huLp : MeasureTheory.MemLp u ∞ (normalizedCubeMeasure Q))
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hderiv : ∀ z ∈ cubeSet Q, ‖fderiv ℝ u z‖ ≤ B) :
    cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) N u ≤
      cubeBesovScaleWeight s Q * (cubeScaleFactor Q * B + cubeLpNorm Q ∞ u) := by
  unfold cubeBesovPartialNormTop
  calc
    cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) N u +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖
        ≤ cubeBesovScaleWeight s Q * cubeScaleFactor Q * B +
            cubeBesovScaleWeight s Q * cubeLpNorm Q ∞ u := by
          exact add_le_add
            (cubeBesovPartialSeminormTop_two_le_scaleWeight_mul_scaleFactor_mul_of_contDiff_bound_of_le_one
              Q u N hs1 hB huLp hu hderiv)
            (mul_le_mul_of_nonneg_left
              (norm_cubeAverage_le_cubeLpNorm_infty Q u huLp)
              (cubeBesovScaleWeight_nonneg s Q))
    _ = cubeBesovScaleWeight s Q * (cubeScaleFactor Q * B + cubeLpNorm Q ∞ u) := by
          ring

theorem cubeBesovDualTestNorm_two_one_le_scaleWeight_mul_of_contDiff_bound_of_le_one
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) (N : ℕ) {s B : ℝ}
    (hs1 : s ≤ 1) (hB : 0 ≤ B)
    (huLp : MeasureTheory.MemLp u ∞ (normalizedCubeMeasure Q))
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hderiv : ∀ z ∈ cubeSet Q, ‖fderiv ℝ u z‖ ≤ B) :
    cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N u ≤
      cubeBesovScaleWeight s Q * (cubeScaleFactor Q * B + cubeLpNorm Q ∞ u) := by
  have hq : cubeBesovConjExponent (1 : ℝ≥0∞) = ∞ := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (1 : ℝ≥0∞)) (q := (∞ : ℝ≥0∞)))
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  rw [cubeBesovDualTestNorm_of_conjExponent_eq_top Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N u hq]
  rw [hpConj]
  exact cubeBesovPartialNormTop_two_le_scaleWeight_mul_of_contDiff_bound_of_le_one
    Q u N hs1 hB huLp hu hderiv

theorem cubeBesovDualTestNorm_one_two_component_le_of_contDiff_component_bound {d : ℕ}
    (Q : TriadicCube d) (ξ : Vec d → Vec d) (i : Fin d) (N : ℕ) {B : ℝ}
    (hB : 0 ≤ B)
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B) :
    cubeBesovDualTestNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => ξ x i) ≤
      B + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ ξ := by
  have hcompLp : MeasureTheory.MemLp (fun x => ξ x i) ∞ (normalizedCubeMeasure Q) := by
    simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hξLp
  calc
    cubeBesovDualTestNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => ξ x i)
        ≤ B + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ (fun x => ξ x i) := by
            exact cubeBesovDualTestNorm_one_two_le_of_contDiff_bound
              Q (fun x => ξ x i) N hB hcompLp (hξ i) (fun z hz => hderiv i z hz)
    _ ≤ B + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ ξ := by
          exact add_le_add le_rfl <|
            mul_le_mul_of_nonneg_left
              (cubeLpNorm_component_le_cubeLpNorm Q ∞ ξ i hξLp)
              (cubeBesovScaleWeight_nonneg 1 Q)


end

end Homogenization
