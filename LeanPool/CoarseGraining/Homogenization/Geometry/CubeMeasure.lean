/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import LeanPool.CoarseGraining.Homogenization.Geometry.BoundaryLayer

/-! # Cube Measure -/

namespace Homogenization

private theorem cubeScaleFactor_pos {d : ℕ} (Q : TriadicCube d) :
    0 < cubeScaleFactor Q := by
  simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)

private theorem measurableSet_coord_halfOpenStrip {d : ℕ} (i : Fin d) (a b : ℝ) :
    MeasurableSet {x : Vec d | a ≤ x i ∧ x i < b} := by
  refine MeasurableSet.inter ?_ ?_
  · exact (isClosed_le continuous_const (continuous_apply i)).measurableSet
  · exact (isOpen_lt (continuous_apply i) continuous_const).measurableSet

private theorem measurableSet_coord_openStrip {d : ℕ} (i : Fin d) (a b : ℝ) :
    MeasurableSet {x : Vec d | a < x i ∧ x i < b} := by
  refine MeasurableSet.inter ?_ ?_
  · exact (isOpen_lt continuous_const (continuous_apply i)).measurableSet
  · exact (isOpen_lt (continuous_apply i) continuous_const).measurableSet

theorem measurableSet_cubeSet {d : ℕ} (Q : TriadicCube d) :
    MeasurableSet (cubeSet Q) := by
  classical
  simpa [cubeSet, Set.iInter_ofPred] using
    (MeasurableSet.iInter fun i : Fin d =>
      measurableSet_coord_halfOpenStrip i
        ((((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q))
        ((((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q)))

theorem measurableSet_openCubeSet {d : ℕ} (Q : TriadicCube d) :
    MeasurableSet (openCubeSet Q) := by
  classical
  simpa [openCubeSet, Set.iInter_ofPred] using
    (MeasurableSet.iInter fun i : Fin d =>
      measurableSet_coord_openStrip i
        ((((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q))
        ((((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q)))

theorem measurableSet_cubeBoundary {d : ℕ} (Q : TriadicCube d) :
    MeasurableSet (cubeBoundary Q) := by
  simpa [cubeBoundary] using (measurableSet_cubeSet Q).diff (measurableSet_openCubeSet Q)

theorem measurableSet_cubeShrunkSet {d : ℕ} (Q : TriadicCube d) (t : ℝ) :
    MeasurableSet (cubeShrunkSet Q t) := by
  classical
  simpa [cubeShrunkSet, Set.iInter_ofPred] using
    (MeasurableSet.iInter fun i : Fin d =>
      measurableSet_coord_halfOpenStrip i
        ((((Q.index i : ℝ) - (1 / 2 : ℝ)) + t) * cubeScaleFactor Q)
        (((((Q.index i : ℝ) + (1 / 2 : ℝ)) - t) * cubeScaleFactor Q)))

theorem measurableSet_cubeBoundaryLayer {d : ℕ} (Q : TriadicCube d) (t : ℝ) :
    MeasurableSet (cubeBoundaryLayer Q t) := by
  simpa [cubeBoundaryLayer] using
    (measurableSet_cubeSet Q).diff (measurableSet_cubeShrunkSet Q t)

theorem cubeSet_eq_pi_Ico {d : ℕ} (Q : TriadicCube d) :
    cubeSet Q =
      Set.pi Set.univ
        (fun i : Fin d =>
          Set.Ico
            ((((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q))
            ((((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q))) := by
  ext x
  simp [cubeSet]

theorem openCubeSet_eq_pi_Ioo {d : ℕ} (Q : TriadicCube d) :
    openCubeSet Q =
      Set.pi Set.univ
        (fun i : Fin d =>
          Set.Ioo
            ((((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q))
            ((((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q))) := by
  ext x
  simp [openCubeSet]

theorem cubeShrunkSet_eq_pi_Ico {d : ℕ} (Q : TriadicCube d) (t : ℝ) :
    cubeShrunkSet Q t =
      Set.pi Set.univ
        (fun i : Fin d =>
          Set.Ico
            (((((Q.index i : ℝ) - (1 / 2 : ℝ)) + t) * cubeScaleFactor Q))
            (((((Q.index i : ℝ) + (1 / 2 : ℝ)) - t) * cubeScaleFactor Q))) := by
  ext x
  simp [cubeShrunkSet]

theorem cubeSet_ae_eq_openCubeSet {d : ℕ} (Q : TriadicCube d) :
    cubeSet Q =ᵐ[MeasureTheory.volume] openCubeSet Q := by
  rw [cubeSet_eq_pi_Ico, openCubeSet_eq_pi_Ioo]
  exact (MeasureTheory.Measure.univ_pi_Ico_ae_eq_Icc (f := fun i : Fin d =>
      (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q))
      (g := fun i : Fin d =>
      (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q))).trans
    (MeasureTheory.Measure.univ_pi_Ioo_ae_eq_Icc (f := fun i : Fin d =>
      (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q))
      (g := fun i : Fin d =>
      (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q))).symm

theorem volume_restrict_cubeSet_eq_volume_restrict_openCubeSet {d : ℕ} (Q : TriadicCube d) :
    MeasureTheory.volume.restrict (cubeSet Q) =
      MeasureTheory.volume.restrict (openCubeSet Q) :=
  MeasureTheory.Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet Q)

theorem ae_restrict_cubeSet_iff {d : ℕ} {Q : TriadicCube d} {p : Vec d → Prop} :
    (∀ᵐ x ∂MeasureTheory.volume.restrict (cubeSet Q), p x) ↔
      ∀ᵐ x ∂MeasureTheory.volume.restrict (openCubeSet Q), p x := by
  exact MeasureTheory.ae_restrict_congr_set (cubeSet_ae_eq_openCubeSet Q)

theorem ae_eq_cubeSet_of_mem_descendantsAtDepth_of_ae_eq_openCubeSet
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} {α : Type*}
    {f g : Vec d → α}
    (hR : R ∈ descendantsAtDepth Q j)
    (hfg : f =ᵐ[MeasureTheory.volume.restrict (openCubeSet Q)] g) :
    f =ᵐ[MeasureTheory.volume.restrict (cubeSet R)] g := by
  have hle :
      MeasureTheory.volume.restrict (openCubeSet R) ≤
        MeasureTheory.volume.restrict (openCubeSet Q) :=
    MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume
      (openCubeSet_subset_of_mem_descendantsAtDepth hR)
  have hchildOpen : f =ᵐ[MeasureTheory.volume.restrict (openCubeSet R)] g :=
    hfg.filter_mono (MeasureTheory.ae_mono hle)
  exact (ae_restrict_cubeSet_iff (Q := R)).2 hchildOpen

theorem volume_cubeBoundary_le_cubeSet {d : ℕ} (Q : TriadicCube d) :
    MeasureTheory.volume (cubeBoundary Q) ≤ MeasureTheory.volume (cubeSet Q) := by
  exact MeasureTheory.measure_mono (cubeBoundary_subset_cubeSet Q)

theorem cubeVolume_eq_scaleFactor_pow {d : ℕ} (Q : TriadicCube d) :
    cubeVolume Q = (cubeScaleFactor Q) ^ d := rfl

theorem cubeVolume_eq_pow_scale {d : ℕ} (Q : TriadicCube d) :
    cubeVolume Q = ((3 : ℝ) ^ Q.scale) ^ d := by
  simp [cubeVolume, cubeScaleFactor]

@[simp] theorem volume_cubeSet_toReal {d : ℕ} (Q : TriadicCube d) :
    (MeasureTheory.volume (cubeSet Q)).toReal = cubeVolume Q := by
  let a : Fin d → ℝ := fun i => ((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q
  let b : Fin d → ℝ := fun i => ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q
  have hab : a ≤ b := by
    intro i
    dsimp [a, b]
    nlinarith [cubeScaleFactor_pos Q]
  rw [cubeSet_eq_pi_Ico]
  have hside : ∀ i : Fin d, b i - a i = cubeScaleFactor Q := by
    intro i
    dsimp [a, b]
    ring
  calc
    (MeasureTheory.volume
        (Set.pi Set.univ
          (fun i : Fin d =>
            Set.Ico
              ((((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q))
              ((((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q))))).toReal
        = ∏ i : Fin d, (b i - a i) := by
          simpa [a, b] using Real.volume_pi_Ico_toReal (ι := Fin d) hab
    _ = cubeVolume Q := by
      calc
        ∏ i : Fin d, (b i - a i) = ∏ _i : Fin d, cubeScaleFactor Q := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          exact hside i
        _ = cubeVolume Q := by
          simp [cubeVolume]

@[simp] theorem volume_openCubeSet_toReal {d : ℕ} (Q : TriadicCube d) :
    (MeasureTheory.volume (openCubeSet Q)).toReal = cubeVolume Q := by
  let a : Fin d → ℝ := fun i => ((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q
  let b : Fin d → ℝ := fun i => ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q
  have hab : a ≤ b := by
    intro i
    dsimp [a, b]
    nlinarith [cubeScaleFactor_pos Q]
  rw [openCubeSet_eq_pi_Ioo]
  have hside : ∀ i : Fin d, b i - a i = cubeScaleFactor Q := by
    intro i
    dsimp [a, b]
    ring
  calc
    (MeasureTheory.volume
        (Set.pi Set.univ
          (fun i : Fin d =>
            Set.Ioo
              ((((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q))
              ((((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q))))).toReal
        = ∏ i : Fin d, (b i - a i) := by
          simpa [a, b] using Real.volume_pi_Ioo_toReal (ι := Fin d) hab
    _ = cubeVolume Q := by
      calc
        ∏ i : Fin d, (b i - a i) = ∏ _i : Fin d, cubeScaleFactor Q := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          exact hside i
        _ = cubeVolume Q := by
          simp [cubeVolume]

theorem volume_cubeShrunkSet_toReal_of_le_half {d : ℕ} (Q : TriadicCube d) {t : ℝ}
    (ht : t ≤ (1 / 2 : ℝ)) :
    (MeasureTheory.volume (cubeShrunkSet Q t)).toReal =
      ((1 - 2 * t) * cubeScaleFactor Q) ^ d := by
  let a : Fin d → ℝ :=
    fun i => (((Q.index i : ℝ) - (1 / 2 : ℝ)) + t) * cubeScaleFactor Q
  let b : Fin d → ℝ :=
    fun i => (((Q.index i : ℝ) + (1 / 2 : ℝ)) - t) * cubeScaleFactor Q
  have hab : a ≤ b := by
    intro i
    dsimp [a, b]
    nlinarith [cubeScaleFactor_pos Q, ht]
  rw [cubeShrunkSet_eq_pi_Ico]
  have hside : ∀ i : Fin d, b i - a i = (1 - 2 * t) * cubeScaleFactor Q := by
    intro i
    dsimp [a, b]
    ring
  calc
    (MeasureTheory.volume
        (Set.pi Set.univ
          (fun i : Fin d =>
            Set.Ico
              (((((Q.index i : ℝ) - (1 / 2 : ℝ)) + t) * cubeScaleFactor Q))
              (((((Q.index i : ℝ) + (1 / 2 : ℝ)) - t) * cubeScaleFactor Q))))).toReal
        = ∏ i : Fin d, (b i - a i) := by
          simpa [a, b] using Real.volume_pi_Ico_toReal (ι := Fin d) hab
    _ = ((1 - 2 * t) * cubeScaleFactor Q) ^ d := by
      calc
        ∏ i : Fin d, (b i - a i) =
            ∏ _i : Fin d, ((1 - 2 * t) * cubeScaleFactor Q) := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          exact hside i
        _ = ((1 - 2 * t) * cubeScaleFactor Q) ^ d := by
          simp

theorem cubeVolume_pos {d : ℕ} (Q : TriadicCube d) :
    0 < cubeVolume Q := by
  have hscale : 0 < cubeScaleFactor Q := cubeScaleFactor_pos Q
  simpa [cubeVolume] using pow_pos hscale d

theorem cubeVolume_nonneg {d : ℕ} (Q : TriadicCube d) :
    0 ≤ cubeVolume Q := by
  exact le_of_lt (cubeVolume_pos Q)

theorem volume_cubeSet_lt_top {d : ℕ} (Q : TriadicCube d) :
    MeasureTheory.volume (cubeSet Q) < ⊤ := by
  refine lt_of_le_of_ne le_top ?_
  intro htop
  have htoReal : (MeasureTheory.volume (cubeSet Q)).toReal = 0 := by
    simp [htop]
  rw [volume_cubeSet_toReal] at htoReal
  exact (cubeVolume_pos Q).ne' htoReal

theorem volume_openCubeSet_lt_top {d : ℕ} (Q : TriadicCube d) :
    MeasureTheory.volume (openCubeSet Q) < ⊤ := by
  exact lt_of_le_of_lt
    (MeasureTheory.measure_mono (openCubeSet_subset_cubeSet Q))
    (volume_cubeSet_lt_top Q)

theorem volume_openCubeSet_eq_volume_cubeSet {d : ℕ} (Q : TriadicCube d) :
    MeasureTheory.volume (openCubeSet Q) = MeasureTheory.volume (cubeSet Q) := by
  exact MeasureTheory.measure_congr (cubeSet_ae_eq_openCubeSet Q).symm

theorem volume_cubeBoundaryLayer_toReal_of_nonneg_le_half {d : ℕ}
    (Q : TriadicCube d) {t : ℝ} (ht_nonneg : 0 ≤ t) (ht_half : t ≤ (1 / 2 : ℝ)) :
    (MeasureTheory.volume (cubeBoundaryLayer Q t)).toReal =
      cubeVolume Q - ((1 - 2 * t) * cubeScaleFactor Q) ^ d := by
  have hsub : cubeShrunkSet Q t ⊆ cubeSet Q :=
    cubeShrunkSet_subset_cubeSet Q ht_nonneg
  have hmeas : MeasureTheory.NullMeasurableSet (cubeShrunkSet Q t) MeasureTheory.volume :=
    (measurableSet_cubeShrunkSet Q t).nullMeasurableSet
  have hfinite :
      MeasureTheory.volume (cubeShrunkSet Q t) ≠ ⊤ :=
    MeasureTheory.measure_ne_top_of_subset hsub (volume_cubeSet_lt_top Q).ne
  have hmeasure :
      MeasureTheory.volume (cubeBoundaryLayer Q t) =
        MeasureTheory.volume (cubeSet Q) - MeasureTheory.volume (cubeShrunkSet Q t) := by
    simpa [cubeBoundaryLayer] using
      MeasureTheory.measure_sdiff hsub hmeas hfinite
  have hle :
      MeasureTheory.volume (cubeShrunkSet Q t) ≤ MeasureTheory.volume (cubeSet Q) :=
    MeasureTheory.measure_mono hsub
  rw [hmeasure, ENNReal.toReal_sub_of_le hle (volume_cubeSet_lt_top Q).ne,
    volume_cubeSet_toReal, volume_cubeShrunkSet_toReal_of_le_half Q ht_half]

theorem integrableOn_cubeSet_iff_integrableOn_openCubeSet
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {Q : TriadicCube d} {f : Vec d → E} :
    MeasureTheory.IntegrableOn f (cubeSet Q) MeasureTheory.volume ↔
      MeasureTheory.IntegrableOn f (openCubeSet Q) MeasureTheory.volume := by
  exact MeasureTheory.integrableOn_congr_set_ae (cubeSet_ae_eq_openCubeSet Q)

theorem setIntegral_cubeSet_eq_setIntegral_openCubeSet
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {Q : TriadicCube d} {f : Vec d → E} :
    ∫ x in cubeSet Q, f x ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q, f x ∂MeasureTheory.volume := by
  exact MeasureTheory.setIntegral_congr_set (cubeSet_ae_eq_openCubeSet Q)

theorem volume_cubeBoundary_eq_zero {d : ℕ} (Q : TriadicCube d) :
    MeasureTheory.volume (cubeBoundary Q) = 0 := by
  have hAE : cubeSet Q =ᵐ[MeasureTheory.volume] openCubeSet Q := cubeSet_ae_eq_openCubeSet Q
  have hdiff : MeasureTheory.volume (cubeSet Q \ openCubeSet Q) = 0 :=
    (MeasureTheory.ae_eq_set.mp hAE).1
  simpa [cubeBoundary] using hdiff

theorem volume_cubeBoundaryLayer_zero {d : ℕ} (Q : TriadicCube d) :
    MeasureTheory.volume (cubeBoundaryLayer Q 0) = 0 := by
  simp

end Homogenization
