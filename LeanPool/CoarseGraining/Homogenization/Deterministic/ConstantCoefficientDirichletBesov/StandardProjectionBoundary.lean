/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.StandardProjectionResidual

/-! # Standard Projection Boundary -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-!
# Boundary-crossing centers for projection increments

For one martingale increment, an overlap cube contributes only if it crosses the
standard triadic partition at the increment scale.  This file isolates that
support reduction.  The remaining geometric work is then a finite counting
estimate for the crossing centers.
-/

/-- Overlap centers whose overlap cube is not contained in any standard
descendant at the increment scale `m + 1`. -/
noncomputable def overlapCrossingCentersAtDepth {d : ℕ}
    (Q : TriadicCube d) (j m : ℕ) : Finset (TriadicCube d) := by
  classical
  exact (overlapCentersAtDepth Q j).filter
    (fun S =>
      ∀ R ∈ descendantsAtDepth Q (m + 1), ¬ overlapCubeSet S ⊆ cubeSet R)

theorem mem_overlapCrossingCentersAtDepth_iff {d : ℕ}
    {Q S : TriadicCube d} {j m : ℕ} :
    S ∈ overlapCrossingCentersAtDepth Q j m ↔
      S ∈ overlapCentersAtDepth Q j ∧
        ∀ R ∈ descendantsAtDepth Q (m + 1), ¬ overlapCubeSet S ⊆ cubeSet R := by
  classical
  simp [overlapCrossingCentersAtDepth]

theorem mem_overlapCentersAtDepth_of_mem_overlapCrossingCentersAtDepth {d : ℕ}
    {Q S : TriadicCube d} {j m : ℕ}
    (hS : S ∈ overlapCrossingCentersAtDepth Q j m) :
    S ∈ overlapCentersAtDepth Q j :=
  (mem_overlapCrossingCentersAtDepth_iff.mp hS).1

theorem overlapCrossingCentersAtDepth_subset_overlapCentersAtDepth {d : ℕ}
    (Q : TriadicCube d) (j m : ℕ) :
    overlapCrossingCentersAtDepth Q j m ⊆ overlapCentersAtDepth Q j := by
  intro S hS
  exact mem_overlapCentersAtDepth_of_mem_overlapCrossingCentersAtDepth hS

/-- If an admissible overlap center is not crossing at the increment scale,
then the increment has zero corrected overlap fluctuation on that center. -/
theorem overlapCubeLpNorm_overlapCubeFluctuationVec_cubeIncrementVec_eq_zero_of_not_mem_crossing
    {d : ℕ} {Q S : TriadicCube d} {j m : ℕ} (u : Vec d → Vec d)
    (hS : S ∈ overlapCentersAtDepth Q j)
    (hSnot : S ∉ overlapCrossingCentersAtDepth Q j m) :
    overlapCubeLpNorm S (2 : ℝ≥0∞)
        (overlapCubeFluctuationVec S (cubeIncrementVec Q (m + 1) u)) = 0 := by
  classical
  have hnot :
      ¬ ∀ R ∈ descendantsAtDepth Q (m + 1), ¬ overlapCubeSet S ⊆ cubeSet R := by
    intro hcross
    exact hSnot (mem_overlapCrossingCentersAtDepth_iff.2 ⟨hS, hcross⟩)
  push Not at hnot
  rcases hnot with ⟨R, hR, hsub⟩
  exact
    overlapCubeLpNorm_overlapCubeFluctuationVec_cubeIncrementVec_eq_zero_of_subset_descendant
      (Q := Q) (S := S) (R := R) (m := m) u hR hsub

/-- The overlap-center sum for one increment may be restricted to the crossing
centers.  Non-crossing centers contribute zero by local constancy. -/
theorem overlapCentersAtDepth_sum_cubeIncrementVec_eq_crossing_sum
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d) (j m : ℕ) :
    (overlapCentersAtDepth Q j).sum
        (fun S =>
          (overlapCubeLpNorm S (2 : ℝ≥0∞)
            (overlapCubeFluctuationVec S (cubeIncrementVec Q (m + 1) u))) ^ 2) =
      (overlapCrossingCentersAtDepth Q j m).sum
        (fun S =>
          (overlapCubeLpNorm S (2 : ℝ≥0∞)
            (overlapCubeFluctuationVec S (cubeIncrementVec Q (m + 1) u))) ^ 2) := by
  classical
  symm
  refine
    Finset.sum_subset
      (overlapCrossingCentersAtDepth_subset_overlapCentersAtDepth Q j m) ?_
  intro S hS hSnot
  have hzero :=
    overlapCubeLpNorm_overlapCubeFluctuationVec_cubeIncrementVec_eq_zero_of_not_mem_crossing
      (Q := Q) (S := S) (j := j) (m := m) u hS hSnot
  simp [hzero]

/-- Depth-average form of
`overlapCentersAtDepth_sum_cubeIncrementVec_eq_crossing_sum`. -/
theorem cubeBesovOverlappingPositiveVectorDepthAverage_cubeIncrementVec_eq_crossing_sum
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d) (j m : ℕ) :
    cubeBesovOverlappingPositiveVectorDepthAverage Q
        (cubeIncrementVec Q (m + 1) u) j =
      ((overlapCentersAtDepth Q j).card : ℝ)⁻¹ *
        (overlapCrossingCentersAtDepth Q j m).sum
          (fun S =>
            (overlapCubeLpNorm S (2 : ℝ≥0∞)
              (overlapCubeFluctuationVec S (cubeIncrementVec Q (m + 1) u))) ^ 2) := by
  unfold cubeBesovOverlappingPositiveVectorDepthAverage overlapCentersAverage
  change
    ((overlapCentersAtDepth Q j).card : ℝ)⁻¹ *
        (overlapCentersAtDepth Q j).sum
          (fun S =>
            (overlapCubeLpNorm S (2 : ℝ≥0∞)
              (overlapCubeFluctuationVec S (cubeIncrementVec Q (m + 1) u))) ^ 2) =
      ((overlapCentersAtDepth Q j).card : ℝ)⁻¹ *
        (overlapCrossingCentersAtDepth Q j m).sum
          (fun S =>
            (overlapCubeLpNorm S (2 : ℝ≥0∞)
              (overlapCubeFluctuationVec S (cubeIncrementVec Q (m + 1) u))) ^ 2)
  rw [overlapCentersAtDepth_sum_cubeIncrementVec_eq_crossing_sum]

theorem overlapCoordLower_eq_cubeCoordLower_sub_cubeScaleFactor {d : ℕ}
    (S : TriadicCube d) (i : Fin d) :
    overlapCoordLower S i = cubeCoordLower S i - cubeScaleFactor S := by
  simp [overlapCoordLower, cubeCoordLower]
  ring

theorem overlapCoordUpper_eq_cubeCoordUpper_add_cubeScaleFactor {d : ℕ}
    (S : TriadicCube d) (i : Fin d) :
    overlapCoordUpper S i = cubeCoordUpper S i + cubeScaleFactor S := by
  simp [overlapCoordUpper, cubeCoordUpper]
  ring

/-- If a fine descendant is one fine scale away from every face of a coarser
cube, then its overlap cube is contained in that coarser cube. -/
theorem overlapCubeSet_subset_cubeSet_of_coord_one_scale_separated
    {d : ℕ} {R S : TriadicCube d}
    (hlo :
      ∀ i : Fin d, cubeCoordLower R i + cubeScaleFactor S ≤ cubeCoordLower S i)
    (hhi :
      ∀ i : Fin d, cubeCoordUpper S i + cubeScaleFactor S ≤ cubeCoordUpper R i) :
    overlapCubeSet S ⊆ cubeSet R := by
  intro x hx i
  have hxi := (mem_overlapCubeSet_iff_coord_bounds.mp hx i)
  have hlower :
      cubeCoordLower R i ≤ overlapCoordLower S i := by
    rw [overlapCoordLower_eq_cubeCoordLower_sub_cubeScaleFactor]
    linarith [hlo i]
  have hupper :
      overlapCoordUpper S i ≤ cubeCoordUpper R i := by
    rw [overlapCoordUpper_eq_cubeCoordUpper_add_cubeScaleFactor]
    exact hhi i
  exact ⟨le_trans hlower hxi.1, lt_of_lt_of_le hxi.2 hupper⟩

/-- A one-scale-separated descendant cannot be a crossing center for the
coarser increment partition. -/
theorem not_mem_overlapCrossingCentersAtDepth_of_coord_one_scale_separated
    {d : ℕ} {Q R S : TriadicCube d} {j m : ℕ}
    (hR : R ∈ descendantsAtDepth Q (m + 1))
    (hlo :
      ∀ i : Fin d, cubeCoordLower R i + cubeScaleFactor S ≤ cubeCoordLower S i)
    (hhi :
      ∀ i : Fin d, cubeCoordUpper S i + cubeScaleFactor S ≤ cubeCoordUpper R i) :
    S ∉ overlapCrossingCentersAtDepth Q j m := by
  intro hS
  have hcross := (mem_overlapCrossingCentersAtDepth_iff.mp hS).2
  exact hcross R hR
    (overlapCubeSet_subset_cubeSet_of_coord_one_scale_separated hlo hhi)

/-- Crossing descendants fail the one-fine-scale interior separation from any
coarser descendant that contains their center cube.  This is the boundary-layer
form needed for the cardinality estimate. -/
theorem not_forall_coord_one_scale_separated_of_mem_overlapCrossingCentersAtDepth
    {d : ℕ} {Q R S : TriadicCube d} {j m n : ℕ}
    (hS : S ∈ overlapCrossingCentersAtDepth Q j m)
    (hR : R ∈ descendantsAtDepth Q (m + 1))
    (_hSR : S ∈ descendantsAtDepth R n) :
    ¬ ∀ i : Fin d,
        cubeCoordLower R i + cubeScaleFactor S ≤ cubeCoordLower S i ∧
          cubeCoordUpper S i + cubeScaleFactor S ≤ cubeCoordUpper R i := by
  intro hsep
  exact
    not_mem_overlapCrossingCentersAtDepth_of_coord_one_scale_separated
      (Q := Q) (R := R) (S := S) (j := j) (m := m)
      hR (fun i => (hsep i).1) (fun i => (hsep i).2) hS

/-- An overlap center at depth `j` has an ancestor at any increment depth
`m + 1 ≤ j + 1`. -/
theorem exists_increment_ancestor_of_mem_overlapCentersAtDepth
    {d : ℕ} {Q S : TriadicCube d} {j m : ℕ}
    (hS : S ∈ overlapCentersAtDepth Q j) (hmj : m ≤ j) :
    ∃ R ∈ descendantsAtDepth Q (m + 1),
      S ∈ descendantsAtDepth R (j - m) := by
  have hSdesc : S ∈ descendantsAtDepth Q (j + 1) :=
    mem_descendantsAtDepth_of_mem_overlapCentersAtDepth hS
  have hdepth : j + 1 = (m + 1) + (j - m) := by
    omega
  have hSdesc' : S ∈ descendantsAtDepth Q ((m + 1) + (j - m)) := by
    simpa [hdepth] using hSdesc
  exact exists_descendant_ancestor_at_depth (Q := Q) (R := S)
    (m + 1) (j - m) hSdesc'

/-- A crossing overlap center has a coarser increment ancestor, and relative to
that ancestor it lies in the one-fine-scale boundary layer. -/
theorem exists_increment_ancestor_boundary_layer_of_mem_overlapCrossingCentersAtDepth
    {d : ℕ} {Q S : TriadicCube d} {j m : ℕ}
    (hS : S ∈ overlapCrossingCentersAtDepth Q j m) (hmj : m ≤ j) :
    ∃ R ∈ descendantsAtDepth Q (m + 1),
      S ∈ descendantsAtDepth R (j - m) ∧
        ¬ ∀ i : Fin d,
          cubeCoordLower R i + cubeScaleFactor S ≤ cubeCoordLower S i ∧
            cubeCoordUpper S i + cubeScaleFactor S ≤ cubeCoordUpper R i := by
  rcases exists_increment_ancestor_of_mem_overlapCentersAtDepth
      (Q := Q) (S := S) (j := j) (m := m)
      (mem_overlapCentersAtDepth_of_mem_overlapCrossingCentersAtDepth hS) hmj with
    ⟨R, hR, hSR⟩
  refine ⟨R, hR, hSR, ?_⟩
  exact
    not_forall_coord_one_scale_separated_of_mem_overlapCrossingCentersAtDepth
      (Q := Q) (R := R) (S := S) (j := j) (m := m) (n := j - m)
      hS hR hSR

/-- Descendants of `R` at depth `n` lying in the one-fine-scale boundary layer
of `R`. -/
noncomputable def descendantBoundaryLayerAtDepth {d : ℕ}
    (R : TriadicCube d) (n : ℕ) : Finset (TriadicCube d) := by
  classical
  exact (descendantsAtDepth R n).filter
    (fun S =>
      ¬ ∀ i : Fin d,
        cubeCoordLower R i + cubeScaleFactor S ≤ cubeCoordLower S i ∧
          cubeCoordUpper S i + cubeScaleFactor S ≤ cubeCoordUpper R i)

theorem mem_descendantBoundaryLayerAtDepth_iff {d : ℕ}
    {R S : TriadicCube d} {n : ℕ} :
    S ∈ descendantBoundaryLayerAtDepth R n ↔
      S ∈ descendantsAtDepth R n ∧
        ¬ ∀ i : Fin d,
          cubeCoordLower R i + cubeScaleFactor S ≤ cubeCoordLower S i ∧
            cubeCoordUpper S i + cubeScaleFactor S ≤ cubeCoordUpper R i := by
  classical
  simp [descendantBoundaryLayerAtDepth]

/-- The boundary layer is exactly the union of the descendants sharing at least
one lower or upper coordinate face with the parent cube. -/
theorem mem_descendantBoundaryLayerAtDepth_iff_exists_coord_face {d : ℕ}
    {R S : TriadicCube d} {n : ℕ} :
    S ∈ descendantBoundaryLayerAtDepth R n ↔
      S ∈ descendantsAtDepth R n ∧
        ∃ i : Fin d,
          cubeCoordLower S i = cubeCoordLower R i ∨
            cubeCoordUpper S i = cubeCoordUpper R i := by
  constructor
  · intro hS
    rcases mem_descendantBoundaryLayerAtDepth_iff.mp hS with
      ⟨hdesc, hboundary⟩
    refine ⟨hdesc, ?_⟩
    by_contra hno
    push Not at hno
    have hsep :
        ∀ i : Fin d,
          cubeCoordLower R i + cubeScaleFactor S ≤ cubeCoordLower S i ∧
            cubeCoordUpper S i + cubeScaleFactor S ≤ cubeCoordUpper R i := by
      intro i
      constructor
      · rcases cubeCoordLower_descendant_eq_or_one_scale_le hdesc i with hEq | hSep
        · exact False.elim ((hno i).1 hEq)
        · exact hSep
      · rcases cubeCoordUpper_descendant_eq_or_one_scale_le hdesc i with hEq | hSep
        · exact False.elim ((hno i).2 hEq)
        · exact hSep
    exact hboundary hsep
  · rintro ⟨hdesc, i, hface⟩
    rw [mem_descendantBoundaryLayerAtDepth_iff]
    refine ⟨hdesc, ?_⟩
    intro hsep
    have hscale_pos : 0 < cubeScaleFactor S := cubeScaleFactor_pos' S
    rcases hface with hface | hface
    · have hbad := (hsep i).1
      nlinarith [hbad, hface, hscale_pos]
    · have hbad := (hsep i).2
      nlinarith [hbad, hface, hscale_pos]

private noncomputable def fixedCoordinateFunctionEquiv {α β : Type*}
    [DecidableEq α] (i : α) (a : β) :
    {f : α → β // f i = a} ≃ ({j : α // j ≠ i} → β) where
  toFun f := fun j => f.1 j.1
  invFun g := ⟨fun j => if h : j = i then a else g ⟨j, h⟩, by simp⟩
  left_inv f := by
    ext j
    by_cases h : j = i
    · subst h
      simp [f.2]
    · simp [h]
  right_inv g := by
    funext j
    simp [j.2]

private theorem card_function_fixed_coord_fin_three {d : ℕ}
    (i : Fin d) (a : Fin 3) :
    ((Finset.univ : Finset (Fin d → Fin 3)).filter
        (fun digits => digits i = a)).card = 3 ^ (d - 1) := by
  classical
  rw [← Fintype.card_subtype (fun digits : Fin d → Fin 3 => digits i = a)]
  have hcard := Fintype.card_congr (fixedCoordinateFunctionEquiv i a)
  rw [Fintype.card_fun] at hcard
  have hcompl : Fintype.card {j : Fin d // j ≠ i} = d - 1 := by
    have h := Fintype.card_subtype_compl (fun j : Fin d => j = i)
    simp [Fintype.card_fin] at h ⊢
  simpa [Fintype.card_fin, hcompl] using hcard

theorem cubeCoordLower_child_eq_parent_iff_digit_zero {d : ℕ}
    (R : TriadicCube d) (digits : Fin d → Fin 3) (i : Fin d) :
    cubeCoordLower
        ({ scale := R.scale - 1
           index := fun k => 3 * R.index k + (digits k : ℤ) - 1 } :
          TriadicCube d) i =
      cubeCoordLower R i ↔
        digits i = 0 := by
  constructor
  · intro h
    let C : TriadicCube d :=
      { scale := R.scale - 1
        index := fun k => 3 * R.index k + (digits k : ℤ) - 1 }
    have hcoord := cubeCoordLower_child R digits i
    have hscale_pos : 0 < cubeScaleFactor C := cubeScaleFactor_pos' _
    have hcoord' :
        cubeCoordLower C i =
          cubeCoordLower R i + (((digits i : ℤ) : ℝ)) * cubeScaleFactor C := by
      simpa [C] using hcoord
    have hdigit_real : (((digits i : ℤ) : ℝ)) = 0 := by
      nlinarith [hcoord', h, hscale_pos]
    have hval : (digits i).val = 0 := by
      exact_mod_cast hdigit_real
    exact Fin.ext hval
  · intro h
    have hcoord := cubeCoordLower_child R digits i
    have hdigit_real : (((digits i : ℤ) : ℝ)) = 0 := by
      simp [h]
    rw [hcoord, hdigit_real]
    ring

theorem cubeCoordUpper_child_eq_parent_iff_digit_two {d : ℕ}
    (R : TriadicCube d) (digits : Fin d → Fin 3) (i : Fin d) :
    cubeCoordUpper
        ({ scale := R.scale - 1
           index := fun k => 3 * R.index k + (digits k : ℤ) - 1 } :
          TriadicCube d) i =
      cubeCoordUpper R i ↔
        digits i = 2 := by
  constructor
  · intro h
    let C : TriadicCube d :=
      { scale := R.scale - 1
        index := fun k => 3 * R.index k + (digits k : ℤ) - 1 }
    have hcoord := cubeCoordUpper_child R digits i
    have hscale_pos : 0 < cubeScaleFactor C := cubeScaleFactor_pos' _
    have hdle_int : (digits i : ℤ) ≤ 2 := by
      exact_mod_cast Nat.le_of_lt_succ (digits i).isLt
    have hdiff_nonneg : 0 ≤ (2 : ℝ) - (((digits i : ℤ) : ℝ)) := by
      exact_mod_cast sub_nonneg.mpr hdle_int
    have hcoord' :
        cubeCoordUpper C i =
          cubeCoordUpper R i -
            ((2 : ℝ) - (((digits i : ℤ) : ℝ))) * cubeScaleFactor C := by
      simpa [C] using hcoord
    have hmul_zero :
        ((2 : ℝ) - (((digits i : ℤ) : ℝ))) * cubeScaleFactor C = 0 := by
      nlinarith [hcoord', h]
    have hdiff_real : (2 : ℝ) - (((digits i : ℤ) : ℝ)) = 0 := by
      nlinarith [hmul_zero, hscale_pos, hdiff_nonneg]
    have hdigit_real : (((digits i : ℤ) : ℝ)) = 2 := by
      nlinarith
    have hval : (digits i).val = 2 := by
      exact_mod_cast hdigit_real
    exact Fin.ext hval
  · intro h
    have hcoord := cubeCoordUpper_child R digits i
    have hdigit_real : (((digits i : ℤ) : ℝ)) = 2 := by
      simp [h]
    rw [hcoord, hdigit_real]
    ring

theorem childCubes_lowerFace_card {d : ℕ}
    (R : TriadicCube d) (i : Fin d) :
    ((childCubes R).filter
        (fun S => cubeCoordLower S i = cubeCoordLower R i)).card =
      3 ^ (d - 1) := by
  classical
  let childOf : (Fin d → Fin 3) → TriadicCube d :=
    fun digits =>
      { scale := R.scale - 1
        index := fun k => 3 * R.index k + (digits k : ℤ) - 1 }
  have hinj : Function.Injective childOf := by
    intro a b hab
    funext k
    apply Fin.ext
    have hindex :
        3 * R.index k + (a k : ℤ) - 1 =
          3 * R.index k + (b k : ℤ) - 1 := by
      simpa [childOf] using congrArg (fun S : TriadicCube d => S.index k) hab
    have hcast : (a k : ℤ) = (b k : ℤ) := by omega
    exact Int.ofNat_inj.mp (by simpa using hcast)
  have hfilter :
      (childCubes R).filter
          (fun S => cubeCoordLower S i = cubeCoordLower R i) =
        ((Finset.univ : Finset (Fin d → Fin 3)).filter
            (fun digits => digits i = 0)).image childOf := by
    unfold childCubes
    rw [Finset.filter_image]
    apply congrArg (Finset.image childOf)
    ext digits
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change cubeCoordLower (childOf digits) i = cubeCoordLower R i ↔
      digits i = 0
    simpa [childOf] using
      cubeCoordLower_child_eq_parent_iff_digit_zero R digits i
  rw [hfilter, Finset.card_image_of_injective]
  · exact card_function_fixed_coord_fin_three i 0
  · exact hinj

theorem childCubes_upperFace_card {d : ℕ}
    (R : TriadicCube d) (i : Fin d) :
    ((childCubes R).filter
        (fun S => cubeCoordUpper S i = cubeCoordUpper R i)).card =
      3 ^ (d - 1) := by
  classical
  let childOf : (Fin d → Fin 3) → TriadicCube d :=
    fun digits =>
      { scale := R.scale - 1
        index := fun k => 3 * R.index k + (digits k : ℤ) - 1 }
  have hinj : Function.Injective childOf := by
    intro a b hab
    funext k
    apply Fin.ext
    have hindex :
        3 * R.index k + (a k : ℤ) - 1 =
          3 * R.index k + (b k : ℤ) - 1 := by
      simpa [childOf] using congrArg (fun S : TriadicCube d => S.index k) hab
    have hcast : (a k : ℤ) = (b k : ℤ) := by omega
    exact Int.ofNat_inj.mp (by simpa using hcast)
  have hfilter :
      (childCubes R).filter
          (fun S => cubeCoordUpper S i = cubeCoordUpper R i) =
        ((Finset.univ : Finset (Fin d → Fin 3)).filter
            (fun digits => digits i = 2)).image childOf := by
    unfold childCubes
    rw [Finset.filter_image]
    apply congrArg (Finset.image childOf)
    ext digits
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change cubeCoordUpper (childOf digits) i = cubeCoordUpper R i ↔
      digits i = 2
    simpa [childOf] using
      cubeCoordUpper_child_eq_parent_iff_digit_two R digits i
  rw [hfilter, Finset.card_image_of_injective]
  · exact card_function_fixed_coord_fin_three i 2
  · exact hinj

noncomputable def descendantLowerFaceAtDepth {d : ℕ}
    (R : TriadicCube d) (n : ℕ) (i : Fin d) : Finset (TriadicCube d) := by
  classical
  exact (descendantsAtDepth R n).filter
    (fun S => cubeCoordLower S i = cubeCoordLower R i)

theorem mem_descendantLowerFaceAtDepth_iff {d : ℕ}
    {R S : TriadicCube d} {n : ℕ} {i : Fin d} :
    S ∈ descendantLowerFaceAtDepth R n i ↔
      S ∈ descendantsAtDepth R n ∧
        cubeCoordLower S i = cubeCoordLower R i := by
  classical
  simp [descendantLowerFaceAtDepth]

noncomputable def descendantUpperFaceAtDepth {d : ℕ}
    (R : TriadicCube d) (n : ℕ) (i : Fin d) : Finset (TriadicCube d) := by
  classical
  exact (descendantsAtDepth R n).filter
    (fun S => cubeCoordUpper S i = cubeCoordUpper R i)

theorem mem_descendantUpperFaceAtDepth_iff {d : ℕ}
    {R S : TriadicCube d} {n : ℕ} {i : Fin d} :
    S ∈ descendantUpperFaceAtDepth R n i ↔
      S ∈ descendantsAtDepth R n ∧
        cubeCoordUpper S i = cubeCoordUpper R i := by
  classical
  simp [descendantUpperFaceAtDepth]

/-- The coordinate-face union containing the boundary layer. -/
noncomputable def descendantFaceBoundaryAtDepth {d : ℕ}
    (R : TriadicCube d) (n : ℕ) : Finset (TriadicCube d) := by
  classical
  exact (Finset.univ : Finset (Fin d)).biUnion
    (fun i => descendantLowerFaceAtDepth R n i ∪ descendantUpperFaceAtDepth R n i)

theorem descendantBoundaryLayerAtDepth_subset_faceBoundaryAtDepth {d : ℕ}
    (R : TriadicCube d) (n : ℕ) :
    descendantBoundaryLayerAtDepth R n ⊆ descendantFaceBoundaryAtDepth R n := by
  intro S hS
  rcases (mem_descendantBoundaryLayerAtDepth_iff_exists_coord_face.mp hS) with
    ⟨hdesc, i, hface | hface⟩
  · dsimp [descendantFaceBoundaryAtDepth]
    exact Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ i,
        Finset.mem_union.mpr
          (Or.inl (mem_descendantLowerFaceAtDepth_iff.2 ⟨hdesc, hface⟩))⟩
  · dsimp [descendantFaceBoundaryAtDepth]
    exact Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ i,
        Finset.mem_union.mpr
          (Or.inr (mem_descendantUpperFaceAtDepth_iff.2 ⟨hdesc, hface⟩))⟩

theorem descendantLowerFaceAtDepth_succ_subset_biUnion {d : ℕ}
    (R : TriadicCube d) (n : ℕ) (i : Fin d) :
    descendantLowerFaceAtDepth R (n + 1) i ⊆
      (descendantLowerFaceAtDepth R n i).biUnion
        (fun P => descendantLowerFaceAtDepth P 1 i) := by
  intro S hS
  rcases mem_descendantLowerFaceAtDepth_iff.mp hS with ⟨hSdesc, hSface⟩
  rcases mem_descendantsAtDepth_succ_iff.mp hSdesc with ⟨P, hP, hSPchild⟩
  have hSPdesc : S ∈ descendantsAtDepth P 1 := by
    simpa [descendantsAtDepth_one] using hSPchild
  have hR_le_P : cubeCoordLower R i ≤ cubeCoordLower P i :=
    cubeCoordLower_le_of_mem_descendantsAtDepth hP i
  have hP_le_S : cubeCoordLower P i ≤ cubeCoordLower S i :=
    cubeCoordLower_le_of_mem_descendantsAtDepth hSPdesc i
  have hPface : cubeCoordLower P i = cubeCoordLower R i := by
    linarith
  have hSfaceP : cubeCoordLower S i = cubeCoordLower P i := by
    linarith
  exact Finset.mem_biUnion.mpr
    ⟨P,
      mem_descendantLowerFaceAtDepth_iff.2 ⟨hP, hPface⟩,
      mem_descendantLowerFaceAtDepth_iff.2 ⟨hSPdesc, hSfaceP⟩⟩

theorem descendantUpperFaceAtDepth_succ_subset_biUnion {d : ℕ}
    (R : TriadicCube d) (n : ℕ) (i : Fin d) :
    descendantUpperFaceAtDepth R (n + 1) i ⊆
      (descendantUpperFaceAtDepth R n i).biUnion
        (fun P => descendantUpperFaceAtDepth P 1 i) := by
  intro S hS
  rcases mem_descendantUpperFaceAtDepth_iff.mp hS with ⟨hSdesc, hSface⟩
  rcases mem_descendantsAtDepth_succ_iff.mp hSdesc with ⟨P, hP, hSPchild⟩
  have hSPdesc : S ∈ descendantsAtDepth P 1 := by
    simpa [descendantsAtDepth_one] using hSPchild
  have hP_le_R : cubeCoordUpper P i ≤ cubeCoordUpper R i :=
    cubeCoordUpper_le_of_mem_descendantsAtDepth hP i
  have hS_le_P : cubeCoordUpper S i ≤ cubeCoordUpper P i :=
    cubeCoordUpper_le_of_mem_descendantsAtDepth hSPdesc i
  have hPface : cubeCoordUpper P i = cubeCoordUpper R i := by
    linarith
  have hSfaceP : cubeCoordUpper S i = cubeCoordUpper P i := by
    linarith
  exact Finset.mem_biUnion.mpr
    ⟨P,
      mem_descendantUpperFaceAtDepth_iff.2 ⟨hP, hPface⟩,
      mem_descendantUpperFaceAtDepth_iff.2 ⟨hSPdesc, hSfaceP⟩⟩

theorem descendantLowerFaceAtDepth_card_le {d : ℕ}
    (R : TriadicCube d) (n : ℕ) (i : Fin d) :
    (descendantLowerFaceAtDepth R n i).card ≤ (3 ^ (d - 1)) ^ n := by
  induction n generalizing R with
  | zero =>
      dsimp [descendantLowerFaceAtDepth]
      exact Finset.card_filter_le {R} (fun S => cubeCoordLower S i = cubeCoordLower R i)
  | succ n ih =>
      let B : Finset (TriadicCube d) :=
        (descendantLowerFaceAtDepth R n i).biUnion
          (fun P => descendantLowerFaceAtDepth P 1 i)
      have hsubset :
          descendantLowerFaceAtDepth R (n + 1) i ⊆ B := by
        simpa [B] using descendantLowerFaceAtDepth_succ_subset_biUnion R n i
      have hcard_child :
          ∀ P ∈ descendantLowerFaceAtDepth R n i,
            (descendantLowerFaceAtDepth P 1 i).card = 3 ^ (d - 1) := by
        intro P _hP
        simpa [descendantLowerFaceAtDepth] using childCubes_lowerFace_card P i
      calc
        (descendantLowerFaceAtDepth R (n + 1) i).card
            ≤ B.card := Finset.card_le_card hsubset
        _ ≤
            ∑ P ∈ descendantLowerFaceAtDepth R n i,
              (descendantLowerFaceAtDepth P 1 i).card := by
              simpa [B] using
                (Finset.card_biUnion_le
                  (s := descendantLowerFaceAtDepth R n i)
                  (t := fun P => descendantLowerFaceAtDepth P 1 i))
        _ =
            ∑ P ∈ descendantLowerFaceAtDepth R n i, 3 ^ (d - 1) := by
              refine Finset.sum_congr rfl ?_
              intro P hP
              exact hcard_child P hP
        _ =
            (descendantLowerFaceAtDepth R n i).card * 3 ^ (d - 1) := by
              simp
        _ ≤
            (3 ^ (d - 1)) ^ n * 3 ^ (d - 1) :=
              Nat.mul_le_mul_right _ (ih R)
        _ =
            (3 ^ (d - 1)) ^ (n + 1) := by
              rw [pow_succ]

theorem descendantUpperFaceAtDepth_card_le {d : ℕ}
    (R : TriadicCube d) (n : ℕ) (i : Fin d) :
    (descendantUpperFaceAtDepth R n i).card ≤ (3 ^ (d - 1)) ^ n := by
  induction n generalizing R with
  | zero =>
      dsimp [descendantUpperFaceAtDepth]
      exact Finset.card_filter_le {R} (fun S => cubeCoordUpper S i = cubeCoordUpper R i)
  | succ n ih =>
      let B : Finset (TriadicCube d) :=
        (descendantUpperFaceAtDepth R n i).biUnion
          (fun P => descendantUpperFaceAtDepth P 1 i)
      have hsubset :
          descendantUpperFaceAtDepth R (n + 1) i ⊆ B := by
        simpa [B] using descendantUpperFaceAtDepth_succ_subset_biUnion R n i
      have hcard_child :
          ∀ P ∈ descendantUpperFaceAtDepth R n i,
            (descendantUpperFaceAtDepth P 1 i).card = 3 ^ (d - 1) := by
        intro P _hP
        simpa [descendantUpperFaceAtDepth] using childCubes_upperFace_card P i
      calc
        (descendantUpperFaceAtDepth R (n + 1) i).card
            ≤ B.card := Finset.card_le_card hsubset
        _ ≤
            ∑ P ∈ descendantUpperFaceAtDepth R n i,
              (descendantUpperFaceAtDepth P 1 i).card := by
              simpa [B] using
                (Finset.card_biUnion_le
                  (s := descendantUpperFaceAtDepth R n i)
                  (t := fun P => descendantUpperFaceAtDepth P 1 i))
        _ =
            ∑ P ∈ descendantUpperFaceAtDepth R n i, 3 ^ (d - 1) := by
              refine Finset.sum_congr rfl ?_
              intro P hP
              exact hcard_child P hP
        _ =
            (descendantUpperFaceAtDepth R n i).card * 3 ^ (d - 1) := by
              simp
        _ ≤
            (3 ^ (d - 1)) ^ n * 3 ^ (d - 1) :=
              Nat.mul_le_mul_right _ (ih R)
        _ =
            (3 ^ (d - 1)) ^ (n + 1) := by
              rw [pow_succ]

theorem descendantBoundaryLayerAtDepth_card_le {d : ℕ}
    (R : TriadicCube d) (n : ℕ) :
    (descendantBoundaryLayerAtDepth R n).card ≤
      2 * d * (3 ^ (d - 1)) ^ n := by
  classical
  let A : ℕ := (3 ^ (d - 1)) ^ n
  calc
    (descendantBoundaryLayerAtDepth R n).card
        ≤ (descendantFaceBoundaryAtDepth R n).card :=
          Finset.card_le_card
            (descendantBoundaryLayerAtDepth_subset_faceBoundaryAtDepth R n)
    _ ≤
        ∑ i : Fin d,
          (descendantLowerFaceAtDepth R n i ∪
            descendantUpperFaceAtDepth R n i).card := by
          simpa [descendantFaceBoundaryAtDepth] using
            (Finset.card_biUnion_le
              (s := (Finset.univ : Finset (Fin d)))
              (t := fun i =>
                descendantLowerFaceAtDepth R n i ∪
                  descendantUpperFaceAtDepth R n i))
    _ ≤
        ∑ _i : Fin d, 2 * A := by
          refine Finset.sum_le_sum ?_
          intro i _hi
          have hlower : (descendantLowerFaceAtDepth R n i).card ≤ A := by
            simpa [A] using descendantLowerFaceAtDepth_card_le R n i
          have hupper : (descendantUpperFaceAtDepth R n i).card ≤ A := by
            simpa [A] using descendantUpperFaceAtDepth_card_le R n i
          calc
            (descendantLowerFaceAtDepth R n i ∪
                descendantUpperFaceAtDepth R n i).card
                ≤
                  (descendantLowerFaceAtDepth R n i).card +
                    (descendantUpperFaceAtDepth R n i).card :=
                    Finset.card_union_le _ _
            _ ≤ A + A := Nat.add_le_add hlower hupper
            _ = 2 * A := by ring
    _ = 2 * d * A := by
          simp [A]
          ring
    _ = 2 * d * (3 ^ (d - 1)) ^ n := by
          rfl

/-- Boundary-layer descendants over all increment-scale ancestors. -/
noncomputable def incrementBoundaryLayerCentersAtDepth {d : ℕ}
    (Q : TriadicCube d) (j m : ℕ) : Finset (TriadicCube d) := by
  classical
  exact (descendantsAtDepth Q (m + 1)).biUnion
    (fun R => descendantBoundaryLayerAtDepth R (j - m))

theorem incrementBoundaryLayerCentersAtDepth_card_le {d : ℕ}
    (Q : TriadicCube d) (j m : ℕ) :
    (incrementBoundaryLayerCentersAtDepth Q j m).card ≤
      (descendantsAtDepth Q (m + 1)).card *
        (2 * d * (3 ^ (d - 1)) ^ (j - m)) := by
  classical
  calc
    (incrementBoundaryLayerCentersAtDepth Q j m).card
        ≤
          ∑ R ∈ descendantsAtDepth Q (m + 1),
            (descendantBoundaryLayerAtDepth R (j - m)).card := by
          dsimp [incrementBoundaryLayerCentersAtDepth]
          exact Finset.card_biUnion_le
    _ ≤
          ∑ _R ∈ descendantsAtDepth Q (m + 1),
            2 * d * (3 ^ (d - 1)) ^ (j - m) := by
          refine Finset.sum_le_sum ?_
          intro R _hR
          exact descendantBoundaryLayerAtDepth_card_le R (j - m)
    _ =
          (descendantsAtDepth Q (m + 1)).card *
            (2 * d * (3 ^ (d - 1)) ^ (j - m)) := by
          simp

theorem incrementBoundaryLayerCentersAtDepth_card_le_pow {d : ℕ}
    (Q : TriadicCube d) (j m : ℕ) :
    (incrementBoundaryLayerCentersAtDepth Q j m).card ≤
      (3 ^ d) ^ (m + 1) *
        (2 * d * (3 ^ (d - 1)) ^ (j - m)) := by
  have h := incrementBoundaryLayerCentersAtDepth_card_le Q j m
  rw [descendantsAtDepth_card Q (m + 1)] at h
  exact h

private theorem finset_sum_biUnion_le_sum_of_nonneg
    {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : α → Finset β) (F : β → ℝ)
    (hF : ∀ x ∈ s.biUnion t, 0 ≤ F x) :
    (s.biUnion t).sum F ≤ ∑ a ∈ s, (t a).sum F := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have hF_s : ∀ x ∈ s.biUnion t, 0 ≤ F x := by
        intro x hx
        exact hF x (by simpa using Finset.mem_union.mpr (Or.inr hx))
      have hinter_nonneg : 0 ≤ ∑ x ∈ t a ∩ s.biUnion t, F x := by
        exact Finset.sum_nonneg (fun x hx =>
          hF x (by
            have hx_left : x ∈ t a := (Finset.mem_inter.mp hx).1
            simp [hx_left]))
      have hunion_le :
          (t a ∪ s.biUnion t).sum F ≤ (t a).sum F + (s.biUnion t).sum F := by
        have h :=
          Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := F)
        linarith
      calc
        ((insert a s).biUnion t).sum F
            = (t a ∪ s.biUnion t).sum F := by
              simp
        _ ≤ (t a).sum F + (s.biUnion t).sum F := hunion_le
        _ ≤ (t a).sum F + ∑ a' ∈ s, (t a').sum F := by
              have hih := ih hF_s
              linarith
        _ = ∑ a' ∈ insert a s, (t a').sum F := by
              simp [ha]

theorem incrementBoundaryLayerCentersAtDepth_sum_le_ancestor_boundaryLayer_sum
    {d : ℕ} (Q : TriadicCube d) (j m : ℕ) (F : TriadicCube d → ℝ)
    (hF : ∀ S ∈ incrementBoundaryLayerCentersAtDepth Q j m, 0 ≤ F S) :
    (incrementBoundaryLayerCentersAtDepth Q j m).sum F ≤
      ∑ R ∈ descendantsAtDepth Q (m + 1),
        (descendantBoundaryLayerAtDepth R (j - m)).sum F := by
  dsimp [incrementBoundaryLayerCentersAtDepth]
  exact finset_sum_biUnion_le_sum_of_nonneg
    (descendantsAtDepth Q (m + 1))
    (fun R => descendantBoundaryLayerAtDepth R (j - m)) F hF

theorem incrementBoundaryLayerCentersAtDepth_sum_le_ancestor_weighted_sum
    {d : ℕ} (Q : TriadicCube d) (j m : ℕ)
    (F B : TriadicCube d → ℝ)
    (hF : ∀ S ∈ incrementBoundaryLayerCentersAtDepth Q j m, 0 ≤ F S)
    (hbound :
      ∀ R ∈ descendantsAtDepth Q (m + 1),
        ∀ S ∈ descendantBoundaryLayerAtDepth R (j - m), F S ≤ B R) :
    (incrementBoundaryLayerCentersAtDepth Q j m).sum F ≤
      ∑ R ∈ descendantsAtDepth Q (m + 1),
        ((descendantBoundaryLayerAtDepth R (j - m)).card : ℝ) * B R := by
  calc
    (incrementBoundaryLayerCentersAtDepth Q j m).sum F
        ≤
          ∑ R ∈ descendantsAtDepth Q (m + 1),
            (descendantBoundaryLayerAtDepth R (j - m)).sum F :=
          incrementBoundaryLayerCentersAtDepth_sum_le_ancestor_boundaryLayer_sum
            Q j m F hF
    _ ≤
          ∑ R ∈ descendantsAtDepth Q (m + 1),
            ((descendantBoundaryLayerAtDepth R (j - m)).card : ℝ) * B R := by
          refine Finset.sum_le_sum ?_
          intro R hR
          have hinner :=
            Finset.sum_le_card_nsmul
              (descendantBoundaryLayerAtDepth R (j - m)) F (B R)
              (hbound R hR)
          simpa using hinner

theorem incrementBoundaryLayerCentersAtDepth_sum_le_const_mul_ancestor_sum
    {d : ℕ} (Q : TriadicCube d) (j m : ℕ)
    (F B : TriadicCube d → ℝ)
    (hF : ∀ S ∈ incrementBoundaryLayerCentersAtDepth Q j m, 0 ≤ F S)
    (hB : ∀ R ∈ descendantsAtDepth Q (m + 1), 0 ≤ B R)
    (hbound :
      ∀ R ∈ descendantsAtDepth Q (m + 1),
        ∀ S ∈ descendantBoundaryLayerAtDepth R (j - m), F S ≤ B R) :
    (incrementBoundaryLayerCentersAtDepth Q j m).sum F ≤
      (2 * d * (3 ^ (d - 1)) ^ (j - m) : ℝ) *
        ∑ R ∈ descendantsAtDepth Q (m + 1), B R := by
  calc
    (incrementBoundaryLayerCentersAtDepth Q j m).sum F
        ≤
          ∑ R ∈ descendantsAtDepth Q (m + 1),
            ((descendantBoundaryLayerAtDepth R (j - m)).card : ℝ) * B R :=
          incrementBoundaryLayerCentersAtDepth_sum_le_ancestor_weighted_sum
            Q j m F B hF hbound
    _ ≤
          ∑ R ∈ descendantsAtDepth Q (m + 1),
            (2 * d * (3 ^ (d - 1)) ^ (j - m) : ℝ) * B R := by
          refine Finset.sum_le_sum ?_
          intro R hR
          have hcard_nat := descendantBoundaryLayerAtDepth_card_le R (j - m)
          have hcard :
              ((descendantBoundaryLayerAtDepth R (j - m)).card : ℝ) ≤
                (2 * d * (3 ^ (d - 1)) ^ (j - m) : ℝ) := by
            exact_mod_cast hcard_nat
          exact mul_le_mul_of_nonneg_right hcard (hB R hR)
    _ =
          (2 * d * (3 ^ (d - 1)) ^ (j - m) : ℝ) *
            ∑ R ∈ descendantsAtDepth Q (m + 1), B R := by
          rw [Finset.mul_sum]

/-- Every crossing center belongs to the boundary layer of its increment-scale
ancestor. -/
theorem overlapCrossingCentersAtDepth_subset_incrementBoundaryLayerCentersAtDepth
    {d : ℕ} (Q : TriadicCube d) {j m : ℕ} (hmj : m ≤ j) :
    overlapCrossingCentersAtDepth Q j m ⊆
      incrementBoundaryLayerCentersAtDepth Q j m := by
  intro S hS
  rcases exists_increment_ancestor_boundary_layer_of_mem_overlapCrossingCentersAtDepth
      (Q := Q) (S := S) (j := j) (m := m) hS hmj with
    ⟨R, hR, hSR, hboundary⟩
  dsimp [incrementBoundaryLayerCentersAtDepth]
  exact Finset.mem_biUnion.mpr
    ⟨R, hR,
      mem_descendantBoundaryLayerAtDepth_iff.2 ⟨hSR, hboundary⟩⟩

theorem overlapCrossingCentersAtDepth_sum_le_incrementBoundaryLayerCentersAtDepth_sum
    {d : ℕ} (Q : TriadicCube d) {j m : ℕ} (hmj : m ≤ j)
    (F : TriadicCube d → ℝ)
    (hF :
      ∀ S ∈ incrementBoundaryLayerCentersAtDepth Q j m, 0 ≤ F S) :
    (overlapCrossingCentersAtDepth Q j m).sum F ≤
      (incrementBoundaryLayerCentersAtDepth Q j m).sum F := by
  exact
    Finset.sum_le_sum_of_subset_of_nonneg
      (overlapCrossingCentersAtDepth_subset_incrementBoundaryLayerCentersAtDepth
        Q hmj)
      (fun S hS _hSnot => hF S hS)

/-- One-increment depth averages are controlled by the corresponding
boundary-layer sum.  The remaining work is to count that boundary layer. -/
theorem cubeBesovOverlappingPositiveVectorDepthAverage_cubeIncrementVec_le_boundaryLayer_sum
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d) {j m : ℕ}
    (hmj : m ≤ j) :
    cubeBesovOverlappingPositiveVectorDepthAverage Q
        (cubeIncrementVec Q (m + 1) u) j ≤
      ((overlapCentersAtDepth Q j).card : ℝ)⁻¹ *
        (incrementBoundaryLayerCentersAtDepth Q j m).sum
          (fun S =>
            (overlapCubeLpNorm S (2 : ℝ≥0∞)
              (overlapCubeFluctuationVec S (cubeIncrementVec Q (m + 1) u))) ^ 2) := by
  rw [cubeBesovOverlappingPositiveVectorDepthAverage_cubeIncrementVec_eq_crossing_sum]
  have hsum :=
    overlapCrossingCentersAtDepth_sum_le_incrementBoundaryLayerCentersAtDepth_sum
      Q hmj
      (fun S =>
        (overlapCubeLpNorm S (2 : ℝ≥0∞)
          (overlapCubeFluctuationVec S (cubeIncrementVec Q (m + 1) u))) ^ 2)
      (fun S _hS => sq_nonneg _)
  exact mul_le_mul_of_nonneg_left hsum
    (inv_nonneg.mpr (by positivity : 0 ≤ ((overlapCentersAtDepth Q j).card : ℝ)))

/-- One-increment overlap averages are controlled by any nonnegative
increment-ancestor budget which bounds each boundary-layer center of that
ancestor.  This is the counted form of the boundary reduction: the only
remaining analytic work is to provide the pointwise ancestor budget. -/
theorem cubeBesovOverlappingPositiveVectorDepthAverage_cubeIncrementVec_le_const_mul_ancestor_sum
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d) {j m : ℕ}
    (hmj : m ≤ j) (B : TriadicCube d → ℝ)
    (hB : ∀ R ∈ descendantsAtDepth Q (m + 1), 0 ≤ B R)
    (hbound :
      ∀ R ∈ descendantsAtDepth Q (m + 1),
        ∀ S ∈ descendantBoundaryLayerAtDepth R (j - m),
          (overlapCubeLpNorm S (2 : ℝ≥0∞)
            (overlapCubeFluctuationVec S (cubeIncrementVec Q (m + 1) u))) ^ 2 ≤ B R) :
    cubeBesovOverlappingPositiveVectorDepthAverage Q
        (cubeIncrementVec Q (m + 1) u) j ≤
      ((overlapCentersAtDepth Q j).card : ℝ)⁻¹ *
        ((2 * d * (3 ^ (d - 1)) ^ (j - m) : ℝ) *
          ∑ R ∈ descendantsAtDepth Q (m + 1), B R) := by
  let F : TriadicCube d → ℝ := fun S =>
    (overlapCubeLpNorm S (2 : ℝ≥0∞)
      (overlapCubeFluctuationVec S (cubeIncrementVec Q (m + 1) u))) ^ 2
  have hboundary :
      cubeBesovOverlappingPositiveVectorDepthAverage Q
          (cubeIncrementVec Q (m + 1) u) j ≤
        ((overlapCentersAtDepth Q j).card : ℝ)⁻¹ *
          (incrementBoundaryLayerCentersAtDepth Q j m).sum F :=
    cubeBesovOverlappingPositiveVectorDepthAverage_cubeIncrementVec_le_boundaryLayer_sum
      (Q := Q) (u := u) hmj
  have hsum :
      (incrementBoundaryLayerCentersAtDepth Q j m).sum F ≤
        (2 * d * (3 ^ (d - 1)) ^ (j - m) : ℝ) *
          ∑ R ∈ descendantsAtDepth Q (m + 1), B R :=
    incrementBoundaryLayerCentersAtDepth_sum_le_const_mul_ancestor_sum
      Q j m F B
      (fun S _hS => sq_nonneg _)
      hB
      hbound
  exact hboundary.trans
    (mul_le_mul_of_nonneg_left hsum
      (inv_nonneg.mpr (by positivity : 0 ≤ ((overlapCentersAtDepth Q j).card : ℝ))))

/-- Lowering the overlap-center normalization to the explicit standard
cardinality lower bound gives the scale-separated counted form of the
one-increment boundary estimate. -/
theorem cubeBesovOverlappingPositiveVectorDepthAverage_cubeIncrementVec_le_pow_inv_const_mul_ancestor_sum
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d) {j m : ℕ}
    (hmj : m ≤ j) (B : TriadicCube d → ℝ)
    (hB : ∀ R ∈ descendantsAtDepth Q (m + 1), 0 ≤ B R)
    (hbound :
      ∀ R ∈ descendantsAtDepth Q (m + 1),
        ∀ S ∈ descendantBoundaryLayerAtDepth R (j - m),
          (overlapCubeLpNorm S (2 : ℝ≥0∞)
            (overlapCubeFluctuationVec S (cubeIncrementVec Q (m + 1) u))) ^ 2 ≤ B R) :
    cubeBesovOverlappingPositiveVectorDepthAverage Q
        (cubeIncrementVec Q (m + 1) u) j ≤
      (((3 ^ d) ^ j : ℕ) : ℝ)⁻¹ *
        ((2 * d * (3 ^ (d - 1)) ^ (j - m) : ℝ) *
          ∑ R ∈ descendantsAtDepth Q (m + 1), B R) := by
  have hbase :=
    cubeBesovOverlappingPositiveVectorDepthAverage_cubeIncrementVec_le_const_mul_ancestor_sum
      (Q := Q) (u := u) (j := j) (m := m) hmj B hB hbound
  have hcardLower :
      (((3 ^ d) ^ j : ℕ) : ℝ) ≤ ((overlapCentersAtDepth Q j).card : ℝ) := by
    exact_mod_cast pow_le_overlapCentersAtDepth_card Q j
  have hcard_pos : 0 < ((overlapCentersAtDepth Q j).card : ℝ) := by
    exact_mod_cast overlapCentersAtDepth_card_pos Q j
  have hpow_pos : 0 < (((3 ^ d) ^ j : ℕ) : ℝ) := by
    positivity
  have hinv :
      ((overlapCentersAtDepth Q j).card : ℝ)⁻¹ ≤
        (((3 ^ d) ^ j : ℕ) : ℝ)⁻¹ :=
    (inv_le_inv₀ hcard_pos hpow_pos).2 hcardLower
  have hsum_nonneg :
      0 ≤ ∑ R ∈ descendantsAtDepth Q (m + 1), B R :=
    Finset.sum_nonneg (fun R hR => hB R hR)
  have hbudget_nonneg :
      0 ≤
        (2 * d * (3 ^ (d - 1)) ^ (j - m) : ℝ) *
          ∑ R ∈ descendantsAtDepth Q (m + 1), B R := by
    exact mul_nonneg (by positivity) hsum_nonneg
  exact hbase.trans
    (mul_le_mul_of_nonneg_right hinv hbudget_nonneg)

end

end Homogenization
