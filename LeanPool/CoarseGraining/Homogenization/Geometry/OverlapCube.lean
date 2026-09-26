/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMeasure

/-! # Overlap Cube -/

@[expose] public section

namespace Homogenization

namespace ScalarOverlap

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise

/-- Side length of the overlapping cube centered at the fine-grid cube `S`.
If `S` has scale `k - 1`, this overlapping cube has side length `3^k`. -/
noncomputable def scaleFactor {d : ℕ} (S : TriadicCube d) : ℝ :=
  3 * cubeScaleFactor S

theorem scaleFactor_pos {d : ℕ} (S : TriadicCube d) :
    0 < scaleFactor S := by
  unfold scaleFactor
  exact mul_pos (by norm_num)
    (by
      simpa [cubeScaleFactor] using
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) S.scale))

theorem scaleFactor_nonneg {d : ℕ} (S : TriadicCube d) :
    0 ≤ scaleFactor S :=
  (scaleFactor_pos S).le

/-- The half-open overlapping cube centered at `cubeCenter S` with side length
`3 * cubeScaleFactor S`. -/
def cubeSet {d : ℕ} (S : TriadicCube d) : Set (Vec d) :=
  { x | ∀ i,
      (((S.index i : ℝ) - (3 / 2 : ℝ)) * cubeScaleFactor S ≤ x i) ∧
      (x i < (((S.index i : ℝ) + (3 / 2 : ℝ)) * cubeScaleFactor S)) }

/-- The open overlapping cube with the same center and side length as `cubeSet`. -/
def openCubeSet {d : ℕ} (S : TriadicCube d) : Set (Vec d) :=
  { x | ∀ i,
      (((S.index i : ℝ) - (3 / 2 : ℝ)) * cubeScaleFactor S < x i) ∧
      (x i < (((S.index i : ℝ) + (3 / 2 : ℝ)) * cubeScaleFactor S)) }

theorem measurableSet_coord_halfOpenStrip {d : ℕ}
    (i : Fin d) (a b : ℝ) :
    MeasurableSet {x : Vec d | a ≤ x i ∧ x i < b} := by
  refine MeasurableSet.inter ?_ ?_
  · exact (isClosed_le continuous_const (continuous_apply i)).measurableSet
  · exact (isOpen_lt (continuous_apply i) continuous_const).measurableSet

theorem measurableSet_coord_openStrip {d : ℕ}
    (i : Fin d) (a b : ℝ) :
    MeasurableSet {x : Vec d | a < x i ∧ x i < b} := by
  refine MeasurableSet.inter ?_ ?_
  · exact (isOpen_lt continuous_const (continuous_apply i)).measurableSet
  · exact (isOpen_lt (continuous_apply i) continuous_const).measurableSet

theorem measurableSet_cubeSet {d : ℕ} (S : TriadicCube d) :
    MeasurableSet (cubeSet S) := by
  classical
  simpa [cubeSet, Set.iInter_ofPred] using
    (MeasurableSet.iInter fun i : Fin d =>
      measurableSet_coord_halfOpenStrip i
        ((((S.index i : ℝ) - (3 / 2 : ℝ)) * cubeScaleFactor S))
        ((((S.index i : ℝ) + (3 / 2 : ℝ)) * cubeScaleFactor S)))

theorem measurableSet_openCubeSet {d : ℕ} (S : TriadicCube d) :
    MeasurableSet (openCubeSet S) := by
  classical
  simpa [openCubeSet, Set.iInter_ofPred] using
    (MeasurableSet.iInter fun i : Fin d =>
      measurableSet_coord_openStrip i
        ((((S.index i : ℝ) - (3 / 2 : ℝ)) * cubeScaleFactor S))
        ((((S.index i : ℝ) + (3 / 2 : ℝ)) * cubeScaleFactor S)))

theorem isOpen_openCubeSet {d : ℕ} (S : TriadicCube d) :
    IsOpen (openCubeSet S) := by
  classical
  rw [openCubeSet]
  have hEq :
      {x : Vec d |
        ∀ i : Fin d,
          (((S.index i : ℝ) - (3 / 2 : ℝ)) * cubeScaleFactor S < x i) ∧
          (x i < (((S.index i : ℝ) + (3 / 2 : ℝ)) * cubeScaleFactor S))} =
        (⋂ i : Fin d,
          {x : Vec d |
            (((S.index i : ℝ) - (3 / 2 : ℝ)) * cubeScaleFactor S < x i) ∧
            (x i < (((S.index i : ℝ) + (3 / 2 : ℝ)) * cubeScaleFactor S))}) := by
    ext x
    simp
  rw [hEq]
  exact
    (isOpen_iInter_of_finite fun i : Fin d =>
      (isOpen_lt
        (show Continuous fun _x : Vec d =>
          (((S.index i : ℝ) - (3 / 2 : ℝ)) * cubeScaleFactor S) from continuous_const)
        (continuous_apply i)).inter
        (isOpen_lt (continuous_apply i)
          (show Continuous fun _x : Vec d =>
            (((S.index i : ℝ) + (3 / 2 : ℝ)) * cubeScaleFactor S) from continuous_const)))

theorem cubeSet_eq_pi_Ico {d : ℕ} (S : TriadicCube d) :
    cubeSet S =
      Set.pi Set.univ
        (fun i : Fin d =>
          Set.Ico
            ((((S.index i : ℝ) - (3 / 2 : ℝ)) * cubeScaleFactor S))
            ((((S.index i : ℝ) + (3 / 2 : ℝ)) * cubeScaleFactor S))) := by
  ext x
  simp [cubeSet]

theorem openCubeSet_eq_pi_Ioo {d : ℕ} (S : TriadicCube d) :
    openCubeSet S =
      Set.pi Set.univ
        (fun i : Fin d =>
          Set.Ioo
            ((((S.index i : ℝ) - (3 / 2 : ℝ)) * cubeScaleFactor S))
            ((((S.index i : ℝ) + (3 / 2 : ℝ)) * cubeScaleFactor S))) := by
  ext x
  simp [openCubeSet]

theorem cubeSet_ae_eq_openCubeSet {d : ℕ} (S : TriadicCube d) :
    cubeSet S =ᵐ[MeasureTheory.volume] openCubeSet S := by
  rw [cubeSet_eq_pi_Ico, openCubeSet_eq_pi_Ioo]
  exact (MeasureTheory.Measure.univ_pi_Ico_ae_eq_Icc (f := fun i : Fin d =>
      (((S.index i : ℝ) - (3 / 2 : ℝ)) * cubeScaleFactor S))
      (g := fun i : Fin d =>
      (((S.index i : ℝ) + (3 / 2 : ℝ)) * cubeScaleFactor S))).trans
    (MeasureTheory.Measure.univ_pi_Ioo_ae_eq_Icc (f := fun i : Fin d =>
      (((S.index i : ℝ) - (3 / 2 : ℝ)) * cubeScaleFactor S))
      (g := fun i : Fin d =>
      (((S.index i : ℝ) + (3 / 2 : ℝ)) * cubeScaleFactor S))).symm

theorem volume_restrict_cubeSet_eq_volume_restrict_openCubeSet
    {d : ℕ} (S : TriadicCube d) :
    MeasureTheory.volume.restrict (cubeSet S) =
      MeasureTheory.volume.restrict (openCubeSet S) :=
  MeasureTheory.Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet S)

theorem openCubeSet_subset_cubeSet {d : ℕ} (S : TriadicCube d) :
    openCubeSet S ⊆ cubeSet S := by
  intro x hx i
  exact ⟨le_of_lt (hx i).1, (hx i).2⟩

theorem interior_cubeSet_eq_openCubeSet {d : ℕ} (Q : TriadicCube d) :
    interior (Homogenization.cubeSet Q) = Homogenization.openCubeSet Q := by
  rw [Homogenization.cubeSet_eq_pi_Ico, Homogenization.openCubeSet_eq_pi_Ioo,
    interior_pi_set Set.finite_univ]
  simp [interior_Ico]

def middleChildCube {d : ℕ} (Q : TriadicCube d) : TriadicCube d :=
  { scale := Q.scale - 1
    index := fun i => 3 * Q.index i }

theorem middleChildCube_mem_childCubes {d : ℕ} (Q : TriadicCube d) :
    middleChildCube Q ∈ childCubes Q := by
  simpa [middleChildCube] using middleChild_mem_childCubes Q

@[simp] theorem scaleFactor_middleChildCube {d : ℕ}
    (Q : TriadicCube d) :
    scaleFactor (middleChildCube Q) = cubeScaleFactor Q := by
  have hscale :
      cubeScaleFactor (middleChildCube Q) = cubeScaleFactor Q / 3 := by
    simpa [middleChildCube] using
      cubeScaleFactor_childCube Q (fun _ => (1 : Fin 3))
  unfold scaleFactor
  rw [hscale]
  ring

theorem cubeSet_middleChildCube_eq_cubeSet {d : ℕ} (Q : TriadicCube d) :
    cubeSet (middleChildCube Q) = Homogenization.cubeSet Q := by
  ext x
  constructor
  · intro hx i
    rcases hx i with ⟨hlo, hhi⟩
    have hscale :
        cubeScaleFactor (middleChildCube Q) = cubeScaleFactor Q / 3 := by
      simpa [middleChildCube] using
        cubeScaleFactor_childCube Q (fun _ => (1 : Fin 3))
    have hindex : (((middleChildCube Q).index i : ℤ) : ℝ) =
        3 * (Q.index i : ℝ) := by
      simp [middleChildCube]
    have hlower :
        (((((middleChildCube Q).index i : ℤ) : ℝ) - (3 / 2 : ℝ)) *
            cubeScaleFactor (middleChildCube Q)) =
          (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q) := by
      rw [hscale, hindex]
      ring
    have hupper :
        (((((middleChildCube Q).index i : ℤ) : ℝ) + (3 / 2 : ℝ)) *
            cubeScaleFactor (middleChildCube Q)) =
          (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q) := by
      rw [hscale, hindex]
      ring
    exact ⟨by simpa [hlower] using hlo, by simpa [hupper] using hhi⟩
  · intro hx i
    rcases hx i with ⟨hlo, hhi⟩
    have hscale :
        cubeScaleFactor (middleChildCube Q) = cubeScaleFactor Q / 3 := by
      simpa [middleChildCube] using
        cubeScaleFactor_childCube Q (fun _ => (1 : Fin 3))
    have hindex : (((middleChildCube Q).index i : ℤ) : ℝ) =
        3 * (Q.index i : ℝ) := by
      simp [middleChildCube]
    have hlower :
        (((((middleChildCube Q).index i : ℤ) : ℝ) - (3 / 2 : ℝ)) *
            cubeScaleFactor (middleChildCube Q)) =
          (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q) := by
      rw [hscale, hindex]
      ring
    have hupper :
        (((((middleChildCube Q).index i : ℤ) : ℝ) + (3 / 2 : ℝ)) *
            cubeScaleFactor (middleChildCube Q)) =
          (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q) := by
      rw [hscale, hindex]
      ring
    exact ⟨by simpa [hlower] using hlo, by simpa [hupper] using hhi⟩

theorem cubeSet_middleChildCube_subset_cubeSet {d : ℕ}
    (Q : TriadicCube d) :
    cubeSet (middleChildCube Q) ⊆ Homogenization.cubeSet Q := by
  rw [cubeSet_middleChildCube_eq_cubeSet]

theorem middleChildCube_injective {d : ℕ} :
    Function.Injective (middleChildCube : TriadicCube d → TriadicCube d) := by
  intro Q R hQR
  cases Q with
  | mk scaleQ indexQ =>
  cases R with
  | mk scaleR indexR =>
  simp [middleChildCube] at hQR ⊢
  rcases hQR with ⟨hscale, hindex⟩
  constructor
  · omega
  · funext i
    exact mul_right_cancel₀ (show (3 : ℤ) ≠ 0 by norm_num)
      (by simpa [mul_comm] using congrFun hindex i)

/-- Volume of an overlapping cube. -/
noncomputable def cubeVolume {d : ℕ} (S : TriadicCube d) : ℝ :=
  (scaleFactor S) ^ d

@[simp] theorem cubeVolume_middleChildCube {d : ℕ}
    (Q : TriadicCube d) :
    cubeVolume (middleChildCube Q) = Homogenization.cubeVolume Q := by
  simp [cubeVolume, Homogenization.cubeVolume_eq_scaleFactor_pow]

theorem cubeVolume_pos {d : ℕ} (S : TriadicCube d) :
    0 < cubeVolume S := by
  unfold cubeVolume
  exact pow_pos (scaleFactor_pos S) d

theorem cubeVolume_nonneg {d : ℕ} (S : TriadicCube d) :
    0 ≤ cubeVolume S :=
  (cubeVolume_pos S).le

@[simp] theorem volume_cubeSet_toReal {d : ℕ} (S : TriadicCube d) :
    (MeasureTheory.volume (cubeSet S)).toReal = cubeVolume S := by
  let a : Fin d → ℝ :=
    fun i => ((S.index i : ℝ) - (3 / 2 : ℝ)) * cubeScaleFactor S
  let b : Fin d → ℝ :=
    fun i => ((S.index i : ℝ) + (3 / 2 : ℝ)) * cubeScaleFactor S
  have hscale_pos : 0 < cubeScaleFactor S := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) S.scale)
  have hab : a ≤ b := by
    intro i
    dsimp [a, b]
    nlinarith
  rw [cubeSet_eq_pi_Ico]
  have hside : ∀ i : Fin d, b i - a i = scaleFactor S := by
    intro i
    dsimp [a, b, scaleFactor]
    ring
  calc
    (MeasureTheory.volume
        (Set.pi Set.univ
          (fun i : Fin d =>
            Set.Ico
              ((((S.index i : ℝ) - (3 / 2 : ℝ)) * cubeScaleFactor S))
              ((((S.index i : ℝ) + (3 / 2 : ℝ)) * cubeScaleFactor S))))).toReal
        = ∏ i : Fin d, (b i - a i) := by
          simpa [a, b] using Real.volume_pi_Ico_toReal (ι := Fin d) hab
    _ = cubeVolume S := by
          calc
            ∏ i : Fin d, (b i - a i) =
                ∏ _i : Fin d, scaleFactor S := by
              refine Finset.prod_congr rfl ?_
              intro i hi
              exact hside i
            _ = cubeVolume S := by
              simp [cubeVolume]

@[simp] theorem volume_openCubeSet_toReal {d : ℕ} (S : TriadicCube d) :
    (MeasureTheory.volume (openCubeSet S)).toReal = cubeVolume S := by
  have hmeasure :
      MeasureTheory.volume (cubeSet S) =
        MeasureTheory.volume (openCubeSet S) :=
    MeasureTheory.measure_congr (cubeSet_ae_eq_openCubeSet S)
  rw [← hmeasure, volume_cubeSet_toReal]

theorem volume_cubeSet_lt_top {d : ℕ} (S : TriadicCube d) :
    MeasureTheory.volume (cubeSet S) < ⊤ := by
  refine lt_of_le_of_ne le_top ?_
  intro htop
  have htoReal : (MeasureTheory.volume (cubeSet S)).toReal = 0 := by
    simp [htop]
  rw [volume_cubeSet_toReal] at htoReal
  exact (cubeVolume_pos S).ne' htoReal

/-- Unnormalized measure on an overlapping cube. -/
noncomputable def cubeMeasure {d : ℕ} (S : TriadicCube d) :
    MeasureTheory.Measure (Vec d) :=
  volume.restrict (cubeSet S)

/-- Normalized measure on an overlapping cube. -/
noncomputable def normalizedCubeMeasure {d : ℕ} (S : TriadicCube d) :
    MeasureTheory.Measure (Vec d) :=
  ENNReal.ofReal ((cubeVolume S)⁻¹) • cubeMeasure S

@[simp] theorem cubeMeasure_apply_univ {d : ℕ} (S : TriadicCube d) :
    cubeMeasure S Set.univ = MeasureTheory.volume (cubeSet S) := by
  rw [cubeMeasure, MeasureTheory.Measure.restrict_apply_univ]

@[simp] theorem cubeMeasure_apply_univ_toReal {d : ℕ} (S : TriadicCube d) :
    (cubeMeasure S Set.univ).toReal = cubeVolume S := by
  simp [cubeMeasure]

theorem cubeMeasure_apply_univ_ne_top {d : ℕ} (S : TriadicCube d) :
    cubeMeasure S Set.univ ≠ ∞ := by
  intro htop
  have hzero : (cubeMeasure S Set.univ).toReal = 0 := by
    simp [htop]
  have hvol : (cubeMeasure S Set.univ).toReal = cubeVolume S :=
    cubeMeasure_apply_univ_toReal S
  have : cubeVolume S = 0 := by
    simpa [hvol] using hzero
  exact (cubeVolume_pos S).ne' this

@[simp] theorem cubeMeasure_apply_univ_eq {d : ℕ} (S : TriadicCube d) :
    cubeMeasure S Set.univ = ENNReal.ofReal (cubeVolume S) := by
  exact (ENNReal.toReal_eq_toReal_iff' (cubeMeasure_apply_univ_ne_top S)
    ENNReal.ofReal_ne_top).1 (by
      rw [cubeMeasure_apply_univ_toReal S,
        ENNReal.toReal_ofReal (cubeVolume_nonneg S)])

@[simp] theorem normalizedCubeMeasure_apply_univ {d : ℕ} (S : TriadicCube d) :
    normalizedCubeMeasure S Set.univ = 1 := by
  rw [normalizedCubeMeasure, MeasureTheory.Measure.smul_apply,
    cubeMeasure_apply_univ_eq S]
  rw [ENNReal.ofReal_inv_of_pos (cubeVolume_pos S)]
  have hvol : ENNReal.ofReal (cubeVolume S) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2 (cubeVolume_pos S)
  simpa [smul_eq_mul] using ENNReal.inv_mul_cancel hvol ENNReal.ofReal_ne_top

instance normalizedCubeMeasure.instIsFiniteMeasure {d : ℕ} (S : TriadicCube d) :
    MeasureTheory.IsFiniteMeasure (normalizedCubeMeasure S) where
  measure_univ_lt_top := by
    simp [normalizedCubeMeasure_apply_univ S]

theorem normalizedCubeMeasure_ne_zero {d : ℕ} (S : TriadicCube d) :
    normalizedCubeMeasure S ≠ 0 := by
  intro hzero
  have huniv : normalizedCubeMeasure S Set.univ = 0 := by
    rw [hzero]
    simp
  simp at huniv

theorem lintegral_normalizedCubeMeasure_eq {d : ℕ}
    (S : TriadicCube d) (f : Vec d → ℝ≥0∞) :
    ∫⁻ x, f x ∂(normalizedCubeMeasure S) =
      ENNReal.ofReal ((cubeVolume S)⁻¹) *
        ∫⁻ x in cubeSet S, f x ∂MeasureTheory.volume := by
  rw [normalizedCubeMeasure, cubeMeasure]
  rw [MeasureTheory.lintegral_smul_measure]
  rfl

end

end ScalarOverlap

end Homogenization
