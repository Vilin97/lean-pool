/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Multiscale.NormalizedNorms
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Restrict

/-! # Projection Lp -/

namespace Homogenization

open MeasureTheory.Measure
open scoped ENNReal

/-!
`L^p` wrappers for the projection layer.

This first checkpoint stays deliberately local: it packages the fact that
`cubeProjection` is constant on each active descendant cube, then converts that
pointwise statement into normalized cube `L^p` identities. It also records the
constant-function behavior of `cubeProjection` and `cubeIncrement`.
-/

theorem cubeProjection_ae_eq_cubeAverage_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (f : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j) :
    cubeProjection Q j f =ᵐ[normalizedCubeMeasure R] (fun _ => cubeAverage R f) := by
  rw [normalizedCubeMeasure, Filter.EventuallyEq]
  exact ae_smul_measure
    ((MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet R)).2 <|
      Filter.Eventually.of_forall fun x hx =>
        cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth f hR hx)
    (ENNReal.ofReal ((cubeVolume R)⁻¹))

theorem cubeProjection_ae_eq_cubeAverage_of_mem_descendantsAtScale {d : ℕ}
    {Q R : TriadicCube d} {k : ℤ} (f : Vec d → ℝ) (hk : k ≤ Q.scale)
    (hR : R ∈ descendantsAtScale Q k) :
    cubeProjection Q (Int.toNat (Q.scale - k)) f =ᵐ[normalizedCubeMeasure R]
      (fun _ => cubeAverage R f) := by
  rw [descendantsAtScale_eq_descendantsAtDepth Q hk] at hR
  exact cubeProjection_ae_eq_cubeAverage_of_mem_descendantsAtDepth f hR

theorem cubeLpNorm_cubeProjection_eq_abs_cubeAverage_of_mem_descendantsAtDepth {d : ℕ} {Q R : TriadicCube d}
    {j : ℕ} (p : ℝ≥0∞) (f : Vec d → ℝ) (hR : R ∈ descendantsAtDepth Q j) (hp : p ≠ 0) :
    cubeLpNorm R p (cubeProjection Q j f) = ‖cubeAverage R f‖ := by
  unfold cubeLpNorm
  rw [Gagliardo.integralLpSeminorm_congr_ae
    (cubeProjection_ae_eq_cubeAverage_of_mem_descendantsAtDepth f hR)]
  rw [Gagliardo.integralLpSeminorm_eq_eLpNorm _ _ _
    MeasureTheory.aestronglyMeasurable_const]
  rw [MeasureTheory.eLpNorm_const (cubeAverage R f) hp (normalizedCubeMeasure_ne_zero R),
    normalizedCubeMeasure_apply_univ]
  simp [Gagliardo.integralLpSeminorm_eq_eLpNorm _ _ _
    MeasureTheory.aestronglyMeasurable_const]

theorem cubeLpNorm_cubeProjection_eq_abs_cubeAverage_of_mem_descendantsAtScale {d : ℕ} {Q R : TriadicCube d}
    {k : ℤ} (p : ℝ≥0∞) (f : Vec d → ℝ) (hk : k ≤ Q.scale) (hR : R ∈ descendantsAtScale Q k)
    (hp : p ≠ 0) : cubeLpNorm R p (cubeProjection Q (Int.toNat (Q.scale - k)) f) = ‖cubeAverage R f‖ := by
  unfold cubeLpNorm
  rw [Gagliardo.integralLpSeminorm_congr_ae
    (cubeProjection_ae_eq_cubeAverage_of_mem_descendantsAtScale f hk hR)]
  rw [Gagliardo.integralLpSeminorm_eq_eLpNorm _ _ _
    MeasureTheory.aestronglyMeasurable_const]
  rw [MeasureTheory.eLpNorm_const (cubeAverage R f) hp (normalizedCubeMeasure_ne_zero R),
    normalizedCubeMeasure_apply_univ]
  simp [Gagliardo.integralLpSeminorm_eq_eLpNorm _ _ _
    MeasureTheory.aestronglyMeasurable_const]

theorem cubeProjection_ae_eq_const {d : ℕ} (Q : TriadicCube d) (j : ℕ) (c : ℝ) :
    cubeProjection Q j (fun _ => c) =ᵐ[normalizedCubeMeasure Q] (fun _ => c) := by
  rw [normalizedCubeMeasure, Filter.EventuallyEq]
  exact ae_smul_measure
    ((MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)).2 <|
      Filter.Eventually.of_forall fun x hx =>
        cubeProjection_const_of_mem_cubeSet Q j c hx)
    (ENNReal.ofReal ((cubeVolume Q)⁻¹))

theorem cubeLpNorm_cubeProjection_nonneg {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞) (j : ℕ)
    (f : Vec d → ℝ) : 0 ≤ cubeLpNorm Q p (cubeProjection Q j f) :=
  cubeLpNorm_nonneg Q p (cubeProjection Q j f)

theorem cubeLpNorm_cubeIncrement_nonneg {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞) (j : ℕ)
    (f : Vec d → ℝ) : 0 ≤ cubeLpNorm Q p (cubeIncrement Q j f) :=
  cubeLpNorm_nonneg Q p (cubeIncrement Q j f)

theorem cubeLpNorm_cubeProjection_const {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞) (j : ℕ)
    (c : ℝ) (hp : p ≠ 0) : cubeLpNorm Q p (cubeProjection Q j (fun _ => c)) = ‖c‖ := by
  unfold cubeLpNorm
  rw [Gagliardo.integralLpSeminorm_congr_ae (cubeProjection_ae_eq_const Q j c)]
  rw [Gagliardo.integralLpSeminorm_eq_eLpNorm _ _ _
    MeasureTheory.aestronglyMeasurable_const]
  rw [MeasureTheory.eLpNorm_const c hp (normalizedCubeMeasure_ne_zero Q),
    normalizedCubeMeasure_apply_univ]
  simp [Gagliardo.integralLpSeminorm_eq_eLpNorm _ _ _
    MeasureTheory.aestronglyMeasurable_const]

@[simp] theorem cubeLpNorm_cubeProjection_zero {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞)
    (j : ℕ) : cubeLpNorm Q p (cubeProjection Q j (fun _ => (0 : ℝ))) = 0 := by
  unfold cubeLpNorm
  rw [Gagliardo.integralLpSeminorm_congr_ae (cubeProjection_ae_eq_const Q j (0 : ℝ))]
  simp [Gagliardo.integralLpSeminorm_eq_eLpNorm _ _ _
    MeasureTheory.aestronglyMeasurable_const]

theorem cubeIncrement_ae_eq_zero_const_succ {d : ℕ} (Q : TriadicCube d) (j : ℕ) (c : ℝ) :
    cubeIncrement Q (j + 1) (fun _ => c) =ᵐ[normalizedCubeMeasure Q] (fun _ => (0 : ℝ)) := by
  rw [normalizedCubeMeasure, Filter.EventuallyEq]
  exact ae_smul_measure
    ((MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)).2 <|
      Filter.Eventually.of_forall fun x hx =>
        cubeIncrement_succ_const Q j c x)
    (ENNReal.ofReal ((cubeVolume Q)⁻¹))

theorem cubeLpNorm_cubeIncrement_zero_const {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞)
    (c : ℝ) (hp : p ≠ 0) : cubeLpNorm Q p (cubeIncrement Q 0 (fun _ => c)) = ‖c‖ := by
  simpa [cubeIncrement] using
    cubeLpNorm_cubeProjection_const (Q := Q) (p := p) (j := 0) c hp

@[simp] theorem cubeLpNorm_cubeIncrement_succ_const {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞)
    (j : ℕ) (c : ℝ) : cubeLpNorm Q p (cubeIncrement Q (j + 1) (fun _ => c)) = 0 := by
  unfold cubeLpNorm
  rw [Gagliardo.integralLpSeminorm_congr_ae (cubeIncrement_ae_eq_zero_const_succ Q j c)]
  simp [Gagliardo.integralLpSeminorm_eq_eLpNorm _ _ _
    MeasureTheory.aestronglyMeasurable_const]

@[simp] theorem cubeLpNorm_cubeIncrement_zero {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞)
    (j : ℕ) : cubeLpNorm Q p (cubeIncrement Q j (fun _ => (0 : ℝ))) = 0 := by
  cases j with
  | zero =>
      simp [cubeIncrement, cubeLpNorm_cubeProjection_zero]
  | succ n =>
      simpa [Nat.succ_eq_add_one] using
        cubeLpNorm_cubeIncrement_succ_const (Q := Q) (p := p) (j := n) (c := (0 : ℝ))

end Homogenization
