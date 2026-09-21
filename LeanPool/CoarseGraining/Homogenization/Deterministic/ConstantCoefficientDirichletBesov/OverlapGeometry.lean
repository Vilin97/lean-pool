/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.Basic
import LeanPool.CoarseGraining.Homogenization.Geometry.CubeColoring

/-! # Overlap Geometry -/

namespace Homogenization

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Pointwise

/-- Note-normalized full positive `q = 2` Besov norm for vector fields. -/
noncomputable def cubeBesovPositiveVectorNormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) : ℝ :=
  Real.sqrt (vecNormSq (cubeAverageVec Q F)) +
    cubeBesovPositiveVectorSeminormTwo Q s F

/-!
## Overlapping positive Besov norm

The disjoint descendant norm above is useful elsewhere in Chapter 3, but it is
not the right endpoint for the classical `K(L²,H¹)` interpolation route: it
does not see jumps across the boundaries of the active triadic partition.  The
corrected norm below tests oscillation on overlapping cubes.  At depth `j`, the
centers lie on the grid one generation finer than the cube size.
-/

/-- Side length of the overlapping cube centered at the fine-grid cube `S`.
If `S` has scale `k - 1`, this overlapping cube has side length `3^k`. -/
noncomputable def overlapCubeScaleFactor {d : ℕ} (S : TriadicCube d) : ℝ :=
  3 * cubeScaleFactor S

theorem overlapCubeScaleFactor_pos {d : ℕ} (S : TriadicCube d) :
    0 < overlapCubeScaleFactor S := by
  unfold overlapCubeScaleFactor
  exact mul_pos (by norm_num)
    (by
      simpa [cubeScaleFactor] using
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) S.scale))

theorem overlapCubeScaleFactor_nonneg {d : ℕ} (S : TriadicCube d) :
    0 ≤ overlapCubeScaleFactor S :=
  (overlapCubeScaleFactor_pos S).le

/-- The half-open overlapping cube centered at `cubeCenter S` with side length
`3 * cubeScaleFactor S`. -/
def overlapCubeSet {d : ℕ} (S : TriadicCube d) : Set (Vec d) :=
  { x | ∀ i,
      (((S.index i : ℝ) - (3 / 2 : ℝ)) * cubeScaleFactor S ≤ x i) ∧
      (x i < (((S.index i : ℝ) + (3 / 2 : ℝ)) * cubeScaleFactor S)) }

/-- The open overlapping cube with the same center and side length as
`overlapCubeSet`.  This is the analytic domain used by the local H¹ Poincare
estimate. -/
def openOverlapCubeSet {d : ℕ} (S : TriadicCube d) : Set (Vec d) :=
  { x | ∀ i,
      (((S.index i : ℝ) - (3 / 2 : ℝ)) * cubeScaleFactor S < x i) ∧
      (x i < (((S.index i : ℝ) + (3 / 2 : ℝ)) * cubeScaleFactor S)) }

theorem measurableSet_coord_overlapHalfOpenStrip {d : ℕ}
    (i : Fin d) (a b : ℝ) :
    MeasurableSet {x : Vec d | a ≤ x i ∧ x i < b} := by
  refine MeasurableSet.inter ?_ ?_
  · exact (isClosed_le continuous_const (continuous_apply i)).measurableSet
  · exact (isOpen_lt (continuous_apply i) continuous_const).measurableSet

theorem measurableSet_coord_overlapOpenStrip {d : ℕ}
    (i : Fin d) (a b : ℝ) :
    MeasurableSet {x : Vec d | a < x i ∧ x i < b} := by
  refine MeasurableSet.inter ?_ ?_
  · exact (isOpen_lt continuous_const (continuous_apply i)).measurableSet
  · exact (isOpen_lt (continuous_apply i) continuous_const).measurableSet

theorem measurableSet_overlapCubeSet {d : ℕ} (S : TriadicCube d) :
    MeasurableSet (overlapCubeSet S) := by
  classical
  simpa [overlapCubeSet, Set.iInter_ofPred] using
    (MeasurableSet.iInter fun i : Fin d =>
      measurableSet_coord_overlapHalfOpenStrip i
        ((((S.index i : ℝ) - (3 / 2 : ℝ)) * cubeScaleFactor S))
        ((((S.index i : ℝ) + (3 / 2 : ℝ)) * cubeScaleFactor S)))

theorem measurableSet_openOverlapCubeSet {d : ℕ} (S : TriadicCube d) :
    MeasurableSet (openOverlapCubeSet S) := by
  classical
  simpa [openOverlapCubeSet, Set.iInter_ofPred] using
    (MeasurableSet.iInter fun i : Fin d =>
      measurableSet_coord_overlapOpenStrip i
        ((((S.index i : ℝ) - (3 / 2 : ℝ)) * cubeScaleFactor S))
        ((((S.index i : ℝ) + (3 / 2 : ℝ)) * cubeScaleFactor S)))

theorem isOpen_openOverlapCubeSet {d : ℕ} (S : TriadicCube d) :
    IsOpen (openOverlapCubeSet S) := by
  classical
  rw [openOverlapCubeSet]
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

theorem overlapCubeSet_eq_pi_Ico {d : ℕ} (S : TriadicCube d) :
    overlapCubeSet S =
      Set.pi Set.univ
        (fun i : Fin d =>
          Set.Ico
            ((((S.index i : ℝ) - (3 / 2 : ℝ)) * cubeScaleFactor S))
            ((((S.index i : ℝ) + (3 / 2 : ℝ)) * cubeScaleFactor S))) := by
  ext x
  simp [overlapCubeSet]

theorem openOverlapCubeSet_eq_pi_Ioo {d : ℕ} (S : TriadicCube d) :
    openOverlapCubeSet S =
      Set.pi Set.univ
        (fun i : Fin d =>
          Set.Ioo
            ((((S.index i : ℝ) - (3 / 2 : ℝ)) * cubeScaleFactor S))
            ((((S.index i : ℝ) + (3 / 2 : ℝ)) * cubeScaleFactor S))) := by
  ext x
  simp [openOverlapCubeSet]

theorem overlapCubeSet_ae_eq_openOverlapCubeSet {d : ℕ} (S : TriadicCube d) :
    overlapCubeSet S =ᵐ[MeasureTheory.volume] openOverlapCubeSet S := by
  rw [overlapCubeSet_eq_pi_Ico, openOverlapCubeSet_eq_pi_Ioo]
  exact (MeasureTheory.Measure.univ_pi_Ico_ae_eq_Icc (f := fun i : Fin d =>
      (((S.index i : ℝ) - (3 / 2 : ℝ)) * cubeScaleFactor S))
      (g := fun i : Fin d =>
      (((S.index i : ℝ) + (3 / 2 : ℝ)) * cubeScaleFactor S))).trans
    (MeasureTheory.Measure.univ_pi_Ioo_ae_eq_Icc (f := fun i : Fin d =>
      (((S.index i : ℝ) - (3 / 2 : ℝ)) * cubeScaleFactor S))
      (g := fun i : Fin d =>
      (((S.index i : ℝ) + (3 / 2 : ℝ)) * cubeScaleFactor S))).symm

theorem volume_restrict_overlapCubeSet_eq_volume_restrict_openOverlapCubeSet
    {d : ℕ} (S : TriadicCube d) :
    MeasureTheory.volume.restrict (overlapCubeSet S) =
      MeasureTheory.volume.restrict (openOverlapCubeSet S) :=
  MeasureTheory.Measure.restrict_congr_set (overlapCubeSet_ae_eq_openOverlapCubeSet S)

theorem integrableOn_overlapCubeSet_iff_integrableOn_openOverlapCubeSet
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {S : TriadicCube d} {f : Vec d → E} :
    MeasureTheory.IntegrableOn f (overlapCubeSet S) MeasureTheory.volume ↔
      MeasureTheory.IntegrableOn f (openOverlapCubeSet S) MeasureTheory.volume :=
  MeasureTheory.integrableOn_congr_set_ae (overlapCubeSet_ae_eq_openOverlapCubeSet S)

theorem setIntegral_overlapCubeSet_eq_setIntegral_openOverlapCubeSet
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {S : TriadicCube d} {f : Vec d → E} :
    ∫ x in overlapCubeSet S, f x ∂MeasureTheory.volume =
      ∫ x in openOverlapCubeSet S, f x ∂MeasureTheory.volume :=
  MeasureTheory.setIntegral_congr_set (overlapCubeSet_ae_eq_openOverlapCubeSet S)

theorem openOverlapCubeSet_subset_overlapCubeSet {d : ℕ} (S : TriadicCube d) :
    openOverlapCubeSet S ⊆ overlapCubeSet S := by
  intro x hx i
  exact ⟨le_of_lt (hx i).1, (hx i).2⟩

theorem interior_cubeSet_eq_openCubeSet {d : ℕ} (Q : TriadicCube d) :
    interior (cubeSet Q) = openCubeSet Q := by
  rw [cubeSet_eq_pi_Ico, openCubeSet_eq_pi_Ioo,
    interior_pi_set Set.finite_univ]
  simp [interior_Ico]

theorem overlapCubeScaleFactor_eq_cubeScaleFactor_originCube_succ {d : ℕ}
    (S : TriadicCube d) :
    overlapCubeScaleFactor S = cubeScaleFactor (originCube d (S.scale + 1)) := by
  unfold overlapCubeScaleFactor cubeScaleFactor originCube
  rw [zpow_add₀]
  · ring
  · norm_num

theorem openOverlapCubeSet_eq_translateSet_smul_originCube_zero {d : ℕ}
    (S : TriadicCube d) :
    openOverlapCubeSet S =
      translateSet (cubeCenter S)
        (overlapCubeScaleFactor S • openCubeSet (originCube d 0)) := by
  ext x
  rw [mem_translateSet_iff_sub_mem]
  constructor
  · intro hx
    rw [Set.mem_smul_set]
    refine ⟨(overlapCubeScaleFactor S)⁻¹ • (x - cubeCenter S), ?_, ?_⟩
    · rw [mem_openCubeSet_originCube_iff]
      intro i
      rw [zpow_zero]
      have hxi := hx i
      have hs_pos : 0 < cubeScaleFactor S := by
        simpa [cubeScaleFactor] using
          (zpow_pos (show (0 : ℝ) < 3 by norm_num) S.scale)
      have hos_pos : 0 < overlapCubeScaleFactor S := overlapCubeScaleFactor_pos S
      have hcoeff :
          (overlapCubeScaleFactor S)⁻¹ * ((3 / 2 : ℝ) * cubeScaleFactor S) =
            (1 / 2 : ℝ) := by
        unfold overlapCubeScaleFactor
        field_simp [hs_pos.ne']
      constructor
      · have hlo_sub :
            (-(3 / 2 : ℝ)) * cubeScaleFactor S < x i - cubeCenter S i := by
          simp [cubeCenter]
          nlinarith [hxi.1]
        have hmul := mul_lt_mul_of_pos_left hlo_sub (inv_pos.mpr hos_pos)
        have hright :
            (overlapCubeScaleFactor S)⁻¹ * (x i - cubeCenter S i) =
              (overlapCubeScaleFactor S)⁻¹ * ((x - cubeCenter S) i) := by
          simp
        rw [hright] at hmul
        have htarget :
            (-(1 / 2 : ℝ)) <
              (overlapCubeScaleFactor S)⁻¹ * ((x - cubeCenter S) i) := by
          nlinarith [hcoeff, hmul]
        simpa using htarget
      · have hhi_sub :
            x i - cubeCenter S i < (3 / 2 : ℝ) * cubeScaleFactor S := by
          simp [cubeCenter]
          nlinarith [hxi.2]
        have hmul := mul_lt_mul_of_pos_left hhi_sub (inv_pos.mpr hos_pos)
        have hleft :
            (overlapCubeScaleFactor S)⁻¹ * (x i - cubeCenter S i) =
              (overlapCubeScaleFactor S)⁻¹ * ((x - cubeCenter S) i) := by
          simp
        rw [hleft] at hmul
        have htarget :
            (overlapCubeScaleFactor S)⁻¹ * ((x - cubeCenter S) i) <
              (1 / 2 : ℝ) := by
          nlinarith [hcoeff, hmul]
        simpa using htarget
    · ext i
      simp
      field_simp [(overlapCubeScaleFactor_pos S).ne']
  · intro hx
    rw [Set.mem_smul_set] at hx
    rcases hx with ⟨y, hy, hxy⟩
    intro i
    have hyi := (mem_openCubeSet_originCube_iff.mp hy) i
    rw [zpow_zero] at hyi
    have hos_pos : 0 < overlapCubeScaleFactor S := overlapCubeScaleFactor_pos S
    have hcoord : overlapCubeScaleFactor S * y i = x i - cubeCenter S i := by
      simpa [Pi.sub_apply] using congrFun hxy i
    constructor
    · have hmul := mul_lt_mul_of_pos_left hyi.1 hos_pos
      dsimp [cubeCenter, overlapCubeScaleFactor] at hmul hcoord ⊢
      nlinarith [hmul, hcoord]
    · have hmul := mul_lt_mul_of_pos_left hyi.2 hos_pos
      dsimp [cubeCenter, overlapCubeScaleFactor] at hmul hcoord ⊢
      nlinarith [hmul, hcoord]

/-- Scale-correct mean-zero H¹ coercive estimate on an open overlap cube,
obtained by dilating the unit centered cube estimate by the overlap side length
and translating to the overlap center. -/
noncomputable def openOverlapCubeMeanZeroH1CoerciveEstimate {d : ℕ}
    (S : TriadicCube d) :
    H1CoerciveEstimate (openOverlapCubeSet S) := by
  let a : ℝ := overlapCubeScaleFactor S
  have ha : 0 < a := overlapCubeScaleFactor_pos S
  let hCunit : H1CoerciveEstimate (openCubeSet (originCube d 0)) :=
    originCubeMeanZeroH1CoerciveEstimate d 0
  let hCdil : H1CoerciveEstimate (a • openCubeSet (originCube d 0)) :=
    hCunit.dilate ha
  letI : MeasureTheory.IsFiniteMeasure
      (volumeMeasureOn (a • openCubeSet (originCube d 0))) := by
    have hscale : a = cubeScaleFactor (originCube d (S.scale + 1)) := by
      simpa [a] using overlapCubeScaleFactor_eq_cubeScaleFactor_originCube_succ S
    rw [hscale, ← openCubeSet_originCube_eq_smul_unit d (S.scale + 1)]
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet
        (originCube d (S.scale + 1))).isFiniteMeasure_restrict_volume
  refine
    { fixedValue := a * hCunit.fixedValue
      constant_nonneg := mul_nonneg ha.le hCunit.constant_nonneg
      bound := ?_ }
  rw [openOverlapCubeSet_eq_translateSet_smul_originCube_zero S]
  exact (hCdil.translate (cubeCenter S)).bound

@[simp] theorem openOverlapCubeMeanZeroH1CoerciveEstimate_constant {d : ℕ}
    (S : TriadicCube d) :
    (openOverlapCubeMeanZeroH1CoerciveEstimate S).fixedValue =
      overlapCubeScaleFactor S * (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue := by
  rfl

/-- The middle child of a triadic cube.  It is the child whose center agrees
with the center of the parent. -/
def middleChildCube {d : ℕ} (Q : TriadicCube d) : TriadicCube d :=
  { scale := Q.scale - 1
    index := fun i => 3 * Q.index i }

theorem middleChildCube_mem_childCubes {d : ℕ} (Q : TriadicCube d) :
    middleChildCube Q ∈ childCubes Q := by
  simpa [middleChildCube] using middleChild_mem_childCubes Q

theorem overlapCubeSet_middleChildCube_eq_cubeSet {d : ℕ} (Q : TriadicCube d) :
    overlapCubeSet (middleChildCube Q) = cubeSet Q := by
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

theorem overlapCubeSet_middleChildCube_subset_cubeSet {d : ℕ}
    (Q : TriadicCube d) :
    overlapCubeSet (middleChildCube Q) ⊆ cubeSet Q := by
  rw [overlapCubeSet_middleChildCube_eq_cubeSet]

/-- The iterated middle descendant at depth `n`. -/
def middleDescendant {d : ℕ} (Q : TriadicCube d) : ℕ → TriadicCube d
  | 0 => Q
  | n + 1 => middleChildCube (middleDescendant Q n)

theorem middleDescendant_mem_descendantsAtDepth {d : ℕ}
    (Q : TriadicCube d) :
    ∀ n : ℕ, middleDescendant Q n ∈ descendantsAtDepth Q n
  | 0 => by
      simp [middleDescendant]
  | n + 1 => by
      change middleChildCube (middleDescendant Q n) ∈ descendantsAtDepth Q (n + 1)
      rw [descendantsAtDepth_succ]
      exact Finset.mem_biUnion.mpr
        ⟨middleDescendant Q n,
          middleDescendant_mem_descendantsAtDepth Q n,
          middleChildCube_mem_childCubes (middleDescendant Q n)⟩

theorem overlapCubeSet_middleDescendant_succ_subset_cubeSet {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    overlapCubeSet (middleDescendant Q (j + 1)) ⊆ cubeSet Q := by
  change overlapCubeSet (middleChildCube (middleDescendant Q j)) ⊆ cubeSet Q
  intro x hx
  have hx_mid : x ∈ cubeSet (middleDescendant Q j) :=
    overlapCubeSet_middleChildCube_subset_cubeSet (middleDescendant Q j) hx
  exact cubeSet_subset_of_mem_descendantsAtDepth
    (middleDescendant_mem_descendantsAtDepth Q j) hx_mid

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

theorem cubeColor_index_add_three_le_of_lt {d : ℕ}
    {R S : TriadicCube d} {i : Fin d}
    (hcolor : cubeColor R = cubeColor S) (hlt : R.index i < S.index i) :
    R.index i + 3 ≤ S.index i := by
  have hmod : R.index i ≡ S.index i [ZMOD 3] :=
    (cubeColor_eq_iff_modEq.mp hcolor) i
  rw [Int.modEq_iff_dvd] at hmod
  rcases hmod with ⟨n, hn⟩
  omega

theorem disjoint_overlapCubeSet_of_scale_eq_of_cubeColor_eq_of_ne {d : ℕ}
    {R S : TriadicCube d} (hscale : R.scale = S.scale)
    (hcolor : cubeColor R = cubeColor S) (hneq : R ≠ S) :
    Disjoint (overlapCubeSet R) (overlapCubeSet S) := by
  rw [Set.disjoint_left]
  intro x hxR hxS
  have hindex_ne : ∃ i, R.index i ≠ S.index i := by
    by_contra h
    push Not at h
    apply hneq
    cases R with
    | mk scaleR indexR =>
    cases S with
    | mk scaleS indexS =>
    simp at hscale h ⊢
    exact ⟨hscale, funext h⟩
  rcases hindex_ne with ⟨i, hi⟩
  have hfactor : cubeScaleFactor S = cubeScaleFactor R := by
    simp [cubeScaleFactor, hscale]
  have hfactor_nonneg : 0 ≤ cubeScaleFactor R := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) R.scale).le
  have hxRi := hxR i
  have hxSi := hxS i
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · have hgap : R.index i + 3 ≤ S.index i :=
      cubeColor_index_add_three_le_of_lt hcolor hlt
    have hgap_real : ((R.index i : ℝ) + 3 : ℝ) ≤ (S.index i : ℝ) := by
      exact_mod_cast hgap
    have hsep :
        (((R.index i : ℝ) + (3 / 2 : ℝ)) * cubeScaleFactor R) ≤
          (((S.index i : ℝ) - (3 / 2 : ℝ)) * cubeScaleFactor S) := by
      rw [hfactor]
      have hcoeff :
          (R.index i : ℝ) + (3 / 2 : ℝ) ≤
            (S.index i : ℝ) - (3 / 2 : ℝ) := by
        linarith
      exact mul_le_mul_of_nonneg_right hcoeff hfactor_nonneg
    exact not_lt_of_ge (le_trans hsep (by simpa [hfactor] using hxSi.1)) hxRi.2
  · have hgap : S.index i + 3 ≤ R.index i :=
      cubeColor_index_add_three_le_of_lt hcolor.symm hgt
    have hgap_real : ((S.index i : ℝ) + 3 : ℝ) ≤ (R.index i : ℝ) := by
      exact_mod_cast hgap
    have hsep :
        (((S.index i : ℝ) + (3 / 2 : ℝ)) * cubeScaleFactor S) ≤
          (((R.index i : ℝ) - (3 / 2 : ℝ)) * cubeScaleFactor R) := by
      rw [hfactor]
      have hcoeff :
          (S.index i : ℝ) + (3 / 2 : ℝ) ≤
            (R.index i : ℝ) - (3 / 2 : ℝ) := by
        linarith
      exact mul_le_mul_of_nonneg_right hcoeff hfactor_nonneg
    exact not_lt_of_ge (le_trans hsep hxRi.1) (by simpa [hfactor] using hxSi.2)

/-- Volume of an overlapping cube. -/
noncomputable def overlapCubeVolume {d : ℕ} (S : TriadicCube d) : ℝ :=
  (overlapCubeScaleFactor S) ^ d

theorem overlapCubeVolume_pos {d : ℕ} (S : TriadicCube d) :
    0 < overlapCubeVolume S := by
  unfold overlapCubeVolume
  exact pow_pos (overlapCubeScaleFactor_pos S) d

theorem overlapCubeVolume_nonneg {d : ℕ} (S : TriadicCube d) :
    0 ≤ overlapCubeVolume S :=
  (overlapCubeVolume_pos S).le

@[simp] theorem volume_overlapCubeSet_toReal {d : ℕ} (S : TriadicCube d) :
    (MeasureTheory.volume (overlapCubeSet S)).toReal = overlapCubeVolume S := by
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
  rw [overlapCubeSet_eq_pi_Ico]
  have hside : ∀ i : Fin d, b i - a i = overlapCubeScaleFactor S := by
    intro i
    dsimp [a, b, overlapCubeScaleFactor]
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
    _ = overlapCubeVolume S := by
          calc
            ∏ i : Fin d, (b i - a i) =
                ∏ _i : Fin d, overlapCubeScaleFactor S := by
              refine Finset.prod_congr rfl ?_
              intro i hi
              exact hside i
            _ = overlapCubeVolume S := by
              simp [overlapCubeVolume]

@[simp] theorem volume_openOverlapCubeSet_toReal {d : ℕ} (S : TriadicCube d) :
    (MeasureTheory.volume (openOverlapCubeSet S)).toReal = overlapCubeVolume S := by
  have hmeasure :
      MeasureTheory.volume (overlapCubeSet S) =
        MeasureTheory.volume (openOverlapCubeSet S) :=
    MeasureTheory.measure_congr (overlapCubeSet_ae_eq_openOverlapCubeSet S)
  rw [← hmeasure, volume_overlapCubeSet_toReal]

theorem volume_overlapCubeSet_lt_top {d : ℕ} (S : TriadicCube d) :
    MeasureTheory.volume (overlapCubeSet S) < ⊤ := by
  refine lt_of_le_of_ne le_top ?_
  intro htop
  have htoReal : (MeasureTheory.volume (overlapCubeSet S)).toReal = 0 := by
    simp [htop]
  rw [volume_overlapCubeSet_toReal] at htoReal
  exact (overlapCubeVolume_pos S).ne' htoReal

theorem volume_openOverlapCubeSet_lt_top {d : ℕ} (S : TriadicCube d) :
    MeasureTheory.volume (openOverlapCubeSet S) < ⊤ :=
  lt_of_le_of_lt
    (MeasureTheory.measure_mono (openOverlapCubeSet_subset_overlapCubeSet S))
    (volume_overlapCubeSet_lt_top S)

instance openOverlapCubeSet.instIsFiniteMeasure {d : ℕ} (S : TriadicCube d) :
    MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openOverlapCubeSet S)) := by
  let U : Set (Vec d) := openOverlapCubeSet S
  let : Fact (MeasureTheory.volume U < ⊤) :=
    ⟨by simpa [U] using volume_openOverlapCubeSet_lt_top S⟩
  infer_instance

theorem openOverlapCubeMeanZero_valueL2Norm_le {d : ℕ}
    (S : TriadicCube d) (u : H1Function (openOverlapCubeSet S)) :
    (u.toMeanZero).valueL2Norm ≤
      (overlapCubeScaleFactor S *
          (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue) *
        ‖u.gradToVectorL2‖ := by
  simpa using (openOverlapCubeMeanZeroH1CoerciveEstimate S).bound_subAverage u

/-- Unnormalized measure on an overlapping cube. -/
noncomputable def overlapCubeMeasure {d : ℕ} (S : TriadicCube d) :
    MeasureTheory.Measure (Vec d) :=
  volume.restrict (overlapCubeSet S)

/-- Normalized measure on an overlapping cube. -/
noncomputable def normalizedOverlapCubeMeasure {d : ℕ} (S : TriadicCube d) :
    MeasureTheory.Measure (Vec d) :=
  ENNReal.ofReal ((overlapCubeVolume S)⁻¹) • overlapCubeMeasure S

theorem lintegral_normalizedCubeMeasure_eq {d : ℕ}
    (Q : TriadicCube d) (f : Vec d → ℝ≥0∞) :
    ∫⁻ x, f x ∂(normalizedCubeMeasure Q) =
      ENNReal.ofReal ((cubeVolume Q)⁻¹) *
        ∫⁻ x in cubeSet Q, f x ∂MeasureTheory.volume := by
  rw [normalizedCubeMeasure, cubeMeasure]
  rw [MeasureTheory.lintegral_smul_measure]
  rfl

theorem ae_openCubeSet_normalizedCubeMeasure {d : ℕ} (Q : TriadicCube d) :
    ∀ᵐ x ∂ normalizedCubeMeasure Q, x ∈ openCubeSet Q := by
  have hcube : ∀ᵐ x ∂ cubeMeasure Q, x ∈ openCubeSet Q := by
    rw [cubeMeasure, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
    exact MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet Q)
  simpa [normalizedCubeMeasure] using
    MeasureTheory.Measure.ae_smul_measure hcube
      (ENNReal.ofReal ((cubeVolume Q)⁻¹))

theorem lintegral_normalizedOverlapCubeMeasure_eq {d : ℕ}
    (S : TriadicCube d) (f : Vec d → ℝ≥0∞) :
    ∫⁻ x, f x ∂(normalizedOverlapCubeMeasure S) =
      ENNReal.ofReal ((overlapCubeVolume S)⁻¹) *
        ∫⁻ x in overlapCubeSet S, f x ∂MeasureTheory.volume := by
  rw [normalizedOverlapCubeMeasure, overlapCubeMeasure]
  rw [MeasureTheory.lintegral_smul_measure]
  rfl

@[simp] theorem overlapCubeMeasure_apply_univ {d : ℕ} (S : TriadicCube d) :
    overlapCubeMeasure S Set.univ = MeasureTheory.volume (overlapCubeSet S) := by
  rw [overlapCubeMeasure, MeasureTheory.Measure.restrict_apply_univ]

@[simp] theorem overlapCubeMeasure_apply_univ_toReal {d : ℕ} (S : TriadicCube d) :
    (overlapCubeMeasure S Set.univ).toReal = overlapCubeVolume S := by
  simp [overlapCubeMeasure]

theorem overlapCubeMeasure_apply_univ_ne_top {d : ℕ} (S : TriadicCube d) :
    overlapCubeMeasure S Set.univ ≠ ∞ := by
  intro htop
  have hzero : (overlapCubeMeasure S Set.univ).toReal = 0 := by
    simp [htop]
  have hvol : (overlapCubeMeasure S Set.univ).toReal = overlapCubeVolume S :=
    overlapCubeMeasure_apply_univ_toReal S
  have : overlapCubeVolume S = 0 := by
    simpa [hvol] using hzero
  exact (overlapCubeVolume_pos S).ne' this

@[simp] theorem overlapCubeMeasure_apply_univ_eq {d : ℕ} (S : TriadicCube d) :
    overlapCubeMeasure S Set.univ = ENNReal.ofReal (overlapCubeVolume S) := by
  exact (ENNReal.toReal_eq_toReal_iff' (overlapCubeMeasure_apply_univ_ne_top S)
    ENNReal.ofReal_ne_top).1 (by
      rw [overlapCubeMeasure_apply_univ_toReal S,
        ENNReal.toReal_ofReal (overlapCubeVolume_nonneg S)])

@[simp] theorem normalizedOverlapCubeMeasure_apply_univ {d : ℕ} (S : TriadicCube d) :
    normalizedOverlapCubeMeasure S Set.univ = 1 := by
  rw [normalizedOverlapCubeMeasure, MeasureTheory.Measure.smul_apply,
    overlapCubeMeasure_apply_univ_eq S]
  rw [ENNReal.ofReal_inv_of_pos (overlapCubeVolume_pos S)]
  have hvol : ENNReal.ofReal (overlapCubeVolume S) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2 (overlapCubeVolume_pos S)
  exact ENNReal.inv_mul_cancel hvol ENNReal.ofReal_ne_top

instance normalizedOverlapCubeMeasure.instIsFiniteMeasure {d : ℕ} (S : TriadicCube d) :
    MeasureTheory.IsFiniteMeasure (normalizedOverlapCubeMeasure S) where
  measure_univ_lt_top := by
    simp [normalizedOverlapCubeMeasure_apply_univ S]

theorem normalizedOverlapCubeMeasure_ne_zero {d : ℕ} (S : TriadicCube d) :
    normalizedOverlapCubeMeasure S ≠ 0 := by
  intro hzero
  have huniv : normalizedOverlapCubeMeasure S Set.univ = 0 := by
    simp [hzero]
  simp at huniv


end

end Homogenization
