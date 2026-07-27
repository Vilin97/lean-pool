/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.BooleanIsoperimetry.CoherentGap

/-!
# Conway--Guy coherent-gap data

This file instantiates the triangular correction pattern used by the
Conway--Guy distinct-subset-sum sequence.  The recurrence and notation follow
Section 2 of Tom Bohman's 1996 paper on the Conway--Guy sequence.
-/

open scoped BigOperators

namespace BooleanIsoperimetry.CoherentGap

/-- The triangular numbers, indexed from zero. -/
def triangular : ℕ → ℕ
  | 0 => 0
  | index + 1 => triangular index + index + 1

lemma self_le_triangular (index : ℕ) : index ≤ triangular index := by
  induction index with
  | zero => simp [triangular]
  | succ index inductionHypothesis =>
      simp only [triangular]
      omega

lemma triangular_mono : Monotone triangular := by
  intro first second hle
  induction second, hle using Nat.le_induction with
  | base => exact le_rfl
  | succ second hfirst inductionHypothesis =>
      simp only [triangular]
      omega

lemma triangular_strictMono : StrictMono triangular := by
  intro first second hlt
  have hstep : triangular first < triangular (first + 1) := by
    simp only [triangular]
    omega
  exact hstep.trans_le (triangular_mono (by omega))

lemma triangular_add_index (index : ℕ) :
    triangular index + index + 1 = triangular (index + 1) := by
  rfl

theorem guideWitness (dimension : ℕ) :
    ∃ width, dimension - 1 ≤ triangular width :=
  ⟨dimension, (Nat.sub_le dimension 1).trans (self_le_triangular dimension)⟩

/-- The least triangular block containing `dimension - 1`. -/
noncomputable def guide (dimension : ℕ) : ℕ :=
  Nat.find (guideWitness dimension)

lemma guide_upper (dimension : ℕ) :
    dimension - 1 ≤ triangular (guide dimension) :=
  Nat.find_spec (guideWitness dimension)

lemma guide_pos {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    0 < guide dimension := by
  by_contra hnot
  have hzero : guide dimension = 0 := Nat.eq_zero_of_not_pos hnot
  have := guide_upper dimension
  simp [hzero, triangular] at this
  omega

lemma guide_lower {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    triangular (guide dimension - 1) + 2 ≤ dimension := by
  have hpositive := guide_pos hdimension
  have hpred : guide dimension - 1 < guide dimension := by omega
  have hminimal :=
    Nat.find_min (guideWitness dimension) hpred
  have hnot : ¬ dimension - 1 ≤ triangular (guide dimension - 1) := hminimal
  omega

lemma guide_le_dimension {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    guide dimension ≤ dimension := by
  have hpositive := guide_pos hdimension
  have hlower := guide_lower hdimension
  have htriangular := self_le_triangular (guide dimension - 1)
  omega

lemma correction_deep_bound {dimension index : ℕ}
    (hdimension : 2 ≤ dimension)
    (hindex : index < guide dimension - 1) :
    triangular index + index + 3 ≤ dimension := by
  have hindex_le : index + 1 ≤ guide dimension - 1 := by omega
  have htriangular :=
    triangular_mono hindex_le
  have hlower := guide_lower hdimension
  have hstep := triangular_add_index index
  omega

lemma negative_index_ge_guide {dimension index : ℕ}
    (hdimension : 2 ≤ dimension)
    (hindex : index < guide dimension - 1) :
    guide dimension ≤ dimension - triangular index - 1 := by
  have hwidth : 2 ≤ guide dimension := by omega
  have hindex_le : index ≤ guide dimension - 2 := by omega
  have htriangular :=
    triangular_mono hindex_le
  have hlower := guide_lower hdimension
  have hstep :
      triangular (guide dimension - 1) =
        triangular (guide dimension - 2) + (guide dimension - 1) := by
    have : guide dimension - 1 = (guide dimension - 2) + 1 := by omega
    conv_lhs => rw [this, triangular]
    omega
  omega

/-- The positive support of the Conway--Guy principal relation. -/
noncomputable def positiveIndex (offset : ℕ)
    (index : Fin (guide (offset + 2))) : Fin (offset + 2) :=
  ⟨index.val, index.isLt.trans_le (guide_le_dimension (by omega))⟩

/-- The triangular negative support of the Conway--Guy principal relation. -/
noncomputable def negativeIndex (offset : ℕ)
    (index : Fin (guide (offset + 2) - 1)) : Fin (offset + 2) := by
  have hdeep := correction_deep_bound (dimension := offset + 2)
    (index := index.val) (by omega) index.isLt
  exact ⟨offset + 2 - triangular index.val - 1, by omega⟩

/-- The smaller-dimensional certificate lift cancelling one negative support
coordinate of the principal relation. -/
noncomputable def correctionFor (offset : ℕ)
    (index : Fin (guide (offset + 2) - 1)) :
    Correction (offset + 2) where
  sourceOffset := offset + 2 - index.val - 3
  sourceCoordinate := by
    have hdeep := correction_deep_bound (dimension := offset + 2)
      (index := index.val) (by omega) index.isLt
    exact ⟨offset + 2 - triangular index.val - index.val - 3, by omega⟩
  steps := index.val + 2
  steps_pos := by omega
  dimension_eq := by
    have hdeep := correction_deep_bound (dimension := offset + 2)
      (index := index.val) (by omega) index.isLt
    omega

/-- The complete correction list in dimension `offset + 2`. -/
noncomputable def corrections (offset : ℕ) :
    List (Correction (offset + 2)) :=
  List.ofFn (correctionFor offset)

/-- The Conway--Guy triangular-block principal relation. -/
noncomputable def principal (offset : ℕ) : Relation (offset + 2) :=
  (∑ index : Fin (guide (offset + 2)),
      basis (positiveIndex offset index)) -
    ∑ index : Fin (guide (offset + 2) - 1),
      basis (negativeIndex offset index)

lemma coordinateSum_sub {n : ℕ} (first second : Relation n) :
    coordinateSum (first - second) =
      coordinateSum first - coordinateSum second := by
  simp [coordinateSum, Finset.sum_sub_distrib]

lemma coordinateSum_finset_sum {n : ℕ} {α : Type}
    (set : Finset α) (relations : α → Relation n) :
    coordinateSum (∑ index ∈ set, relations index) =
      ∑ index ∈ set, coordinateSum (relations index) := by
  classical
  induction set using Finset.induction_on with
  | empty => simp [coordinateSum]
  | @insert element set hnotMember inductionHypothesis =>
      simp [hnotMember, coordinateSum_add, inductionHypothesis]

@[simp]
lemma coordinateSum_basis {n : ℕ} (coordinate : Fin n) :
    coordinateSum (basis coordinate) = 1 := by
  classical
  simp [coordinateSum, basis]

lemma principal_coordinateSum (offset : ℕ) :
    coordinateSum (principal offset) = 1 := by
  rw [principal, coordinateSum_sub]
  simp only [coordinateSum_finset_sum, coordinateSum_basis,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpositive := guide_pos (dimension := offset + 2) (by omega)
  omega

lemma positiveIndex_injective (offset : ℕ) :
    Function.Injective (positiveIndex offset) := by
  intro first second hequal
  apply Fin.ext
  simpa [positiveIndex] using congrArg Fin.val hequal

lemma negativeIndex_injective (offset : ℕ) :
    Function.Injective (negativeIndex offset) := by
  intro first second hequal
  have hvalue := congrArg Fin.val hequal
  simp only [negativeIndex] at hvalue
  have hfirst := correction_deep_bound (dimension := offset + 2)
    (index := first.val) (by omega) first.isLt
  have hsecond := correction_deep_bound (dimension := offset + 2)
    (index := second.val) (by omega) second.isLt
  have htriangular :
      triangular first.val = triangular second.val := by
    omega
  apply Fin.ext
  exact triangular_strictMono.injective htriangular

lemma positiveIndex_ne_negativeIndex (offset : ℕ)
    (positive : Fin (guide (offset + 2)))
    (negative : Fin (guide (offset + 2) - 1)) :
    positiveIndex offset positive ≠ negativeIndex offset negative := by
  intro hequal
  have hvalue := congrArg Fin.val hequal
  simp only [positiveIndex, negativeIndex] at hvalue
  have hseparated := negative_index_ge_guide (dimension := offset + 2)
    (index := negative.val) (by omega) negative.isLt
  omega

lemma relation_finset_sum_apply {n : ℕ} {α : Type}
    (set : Finset α) (relations : α → Relation n) (coordinate : Fin n) :
    (∑ index ∈ set, relations index) coordinate =
      ∑ index ∈ set, relations index coordinate := by
  classical
  induction set using Finset.induction_on with
  | empty => simp
  | @insert element set hnotMember inductionHypothesis =>
      simp [hnotMember, inductionHypothesis]

lemma sum_basis_apply {sourceDimension targetDimension : ℕ}
    (embedding : Fin sourceDimension → Fin targetDimension)
    (hinjective : Function.Injective embedding)
    (coordinate : Fin targetDimension) :
    (∑ index, basis (embedding index)) coordinate =
      if coordinate ∈ Finset.univ.image embedding then 1 else 0 := by
  classical
  rw [relation_finset_sum_apply]
  calc
    (∑ index, basis (embedding index) coordinate) =
        ∑ imageCoordinate ∈ Finset.univ.image embedding,
          basis imageCoordinate coordinate := by
      symm
      simpa using Finset.sum_image hinjective.injOn
    _ = if coordinate ∈ Finset.univ.image embedding then 1 else 0 := by
      simp [basis]

lemma principal_entry (offset : ℕ) (coordinate : Fin (offset + 2)) :
    principal offset coordinate = -1 ∨
      principal offset coordinate = 0 ∨
      principal offset coordinate = 1 := by
  classical
  rw [principal, Pi.sub_apply]
  rw [sum_basis_apply (positiveIndex offset) (positiveIndex_injective offset)]
  rw [sum_basis_apply (negativeIndex offset) (negativeIndex_injective offset)]
  by_cases hpositive :
      coordinate ∈ Finset.univ.image (positiveIndex offset)
  · have hnegative :
        coordinate ∉ Finset.univ.image (negativeIndex offset) := by
      intro hmember
      rcases Finset.mem_image.mp hpositive with ⟨positive, _, hpositiveEqual⟩
      rcases Finset.mem_image.mp hmember with ⟨negative, _, hnegativeEqual⟩
      exact positiveIndex_ne_negativeIndex offset positive negative
        (hpositiveEqual.trans hnegativeEqual.symm)
    simp [hpositive, hnegative]
  · by_cases hnegative :
        coordinate ∈ Finset.univ.image (negativeIndex offset)
    · simp [hpositive, hnegative]
    · simp [hpositive, hnegative]

lemma lift_sub {n : ℕ} (first second : Relation n) :
    lift (first - second) = lift first - lift second := by
  funext coordinate
  refine Fin.cases ?_ (fun index => ?_) coordinate
  · simp [lift, coordinateSum, Finset.sum_sub_distrib]
    ring
  · simp [lift]

lemma iteratedLift_basis_eq {n : ℕ} (coordinate : Fin n) :
    ∀ {steps : ℕ} (hsteps : 0 < steps),
      iteratedLift (basis coordinate) steps =
        basis (⟨coordinate.val + steps, by omega⟩ : Fin (n + steps)) -
          basis (⟨steps - 1, by omega⟩ : Fin (n + steps))
  | 0, hsteps => by omega
  | 1, _ => by
      change lift (basis coordinate) =
        basis (⟨coordinate.val + 1, by omega⟩ : Fin (n + 1)) -
          basis (⟨1 - 1, by omega⟩ : Fin (n + 1))
      rw [lift_basis]
      have hpositive :
          coordinate.succ =
            (⟨coordinate.val + 1, by omega⟩ : Fin (n + 1)) := by
        apply Fin.ext
        simp
      have hnegative :
          (0 : Fin (n + 1)) =
            (⟨1 - 1, by omega⟩ : Fin (n + 1)) := by
        apply Fin.ext
        simp
      rw [hpositive, hnegative]
  | steps + 2, _ => by
      have inductionHypothesis :=
        iteratedLift_basis_eq coordinate (steps := steps + 1) (by omega)
      rw [iteratedLift, inductionHypothesis, lift_sub, lift_basis, lift_basis]
      have hpositive :
          (⟨coordinate.val + (steps + 1), by omega⟩ :
              Fin (n + (steps + 1))).succ =
            (⟨coordinate.val + (steps + 2), by omega⟩ :
              Fin (n + (steps + 2))) := by
        apply Fin.ext
        simp
        omega
      have hnegative :
          (⟨steps + 1 - 1, by omega⟩ :
              Fin (n + (steps + 1))).succ =
            (⟨steps + 2 - 1, by omega⟩ :
              Fin (n + (steps + 2))) := by
        apply Fin.ext
        simp
      rw [hpositive, hnegative]
      abel

@[simp]
lemma castRelation_apply {firstDimension secondDimension : ℕ}
    (hdimension : firstDimension = secondDimension)
    (relation : Relation firstDimension) (coordinate : Fin secondDimension) :
    castRelation hdimension relation coordinate =
      relation (Fin.cast hdimension.symm coordinate) := by
  subst secondDimension
  rfl

lemma castRelation_sub {firstDimension secondDimension : ℕ}
    (hdimension : firstDimension = secondDimension)
    (first second : Relation firstDimension) :
    castRelation hdimension (first - second) =
      castRelation hdimension first - castRelation hdimension second := by
  subst secondDimension
  rfl

lemma castRelation_basis {firstDimension secondDimension : ℕ}
    (hdimension : firstDimension = secondDimension)
    (coordinate : Fin firstDimension) :
    castRelation hdimension (basis coordinate) =
      basis (Fin.cast hdimension coordinate) := by
  subst secondDimension
  rfl

lemma correctionFor_target (offset : ℕ)
    (index : Fin (guide (offset + 2) - 1)) :
    (correctionFor offset index).target =
      basis (negativeIndex offset index) -
        basis (⟨index.val + 1, by
          have hdeep := correction_deep_bound (dimension := offset + 2)
            (index := index.val) (by omega) index.isLt
          omega⟩ : Fin (offset + 2)) := by
  unfold Correction.target
  rw [iteratedLift_basis_eq (hsteps := by simp [correctionFor])]
  rw [castRelation_sub, castRelation_basis, castRelation_basis]
  congr 1
  · apply congrArg basis
    apply Fin.ext
    simp [correctionFor, negativeIndex]
    have hdeep := correction_deep_bound (dimension := offset + 2)
      (index := index.val) (by omega) index.isLt
    omega

lemma corrections_target_sum (offset : ℕ) :
    ((corrections offset).map Correction.target).sum =
      ∑ index : Fin (guide (offset + 2) - 1),
        (basis (negativeIndex offset index) -
          basis (⟨index.val + 1, by
            have hdeep := correction_deep_bound (dimension := offset + 2)
              (index := index.val) (by omega) index.isLt
            omega⟩ : Fin (offset + 2))) := by
  simp [corrections, List.sum_ofFn, correctionFor_target]

lemma principal_corrections_decomposition (offset : ℕ) :
    principal offset +
        ((corrections offset).map Correction.target).sum =
      basis 0 := by
  rw [principal, corrections_target_sum, Finset.sum_sub_distrib]
  have hpositive := guide_pos (dimension := offset + 2) (by omega)
  have hguide :
      guide (offset + 2) = (guide (offset + 2) - 1) + 1 := by
    omega
  let equivalence :
      Fin ((guide (offset + 2) - 1) + 1) ≃
        Fin (guide (offset + 2)) :=
    Fin.castOrderIso hguide.symm
  have hpartition :
      (∑ index : Fin (guide (offset + 2)),
          basis (positiveIndex offset index)) =
        basis 0 +
          ∑ index : Fin (guide (offset + 2) - 1),
            basis (⟨index.val + 1, by
              have hdeep := correction_deep_bound (dimension := offset + 2)
                (index := index.val) (by omega) index.isLt
              omega⟩ : Fin (offset + 2)) := by
    rw [← equivalence.sum_comp]
    rw [Fin.sum_univ_succ]
    congr 1
  rw [hpartition]
  abel

/-- The one-indexed Conway--Guy recurrence, stored with zero-based indices. -/
def difference (blockGuide : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | index + 1 =>
      ∑ offset ∈ Finset.range (blockGuide (index + 2)),
        difference blockGuide (index - offset)
termination_by index => index
decreasing_by omega

/-- The Conway--Guy difference sequence using the triangular block guide. -/
noncomputable def conwayGuyDifference (index : ℕ) : ℕ :=
  difference guide index

/-- The cumulative Conway--Guy heights. -/
noncomputable def conwayGuyHeight (dimension : ℕ) : ℤ :=
  ∑ index ∈ Finset.range dimension, (conwayGuyDifference index : ℤ)

@[simp]
lemma conwayGuyHeight_zero : conwayGuyHeight 0 = 0 := by
  simp [conwayGuyHeight]

@[simp]
lemma conwayGuyHeight_one : conwayGuyHeight 1 = 1 := by
  simp [conwayGuyHeight, conwayGuyDifference, difference]

lemma conwayGuyHeight_succ (dimension : ℕ) :
    conwayGuyHeight (dimension + 1) =
      conwayGuyHeight dimension + conwayGuyDifference dimension := by
  simp [conwayGuyHeight, Finset.sum_range_succ]

/-- Arithmetic data from which the coherent-gap weight tower is built. -/
structure ConwayGuyArithmetic where
  /-- Block guide for the recurrence. -/
  guide : ℕ → ℕ
  /-- Cumulative heights of the recurrence. -/
  height : ℕ → ℤ
  /-- The zero-dimensional height. -/
  height_zero : height 0 = 0

/-- The arithmetic data of the actual Conway--Guy sequence. -/
noncomputable def conwayGuyArithmetic : ConwayGuyArithmetic where
  guide := guide
  height := conwayGuyHeight
  height_zero := conwayGuyHeight_zero

/-- The increasing Conway--Guy-style row obtained from cumulative heights. -/
def ConwayGuyArithmetic.weights (data : ConwayGuyArithmetic)
    (dimension : ℕ) : Relation dimension :=
  fun coordinate =>
    data.height dimension -
      data.height (dimension - (coordinate.val + 1))

/-- The coordinate adjoined at the front when the dimension increases. -/
def ConwayGuyArithmetic.head (data : ConwayGuyArithmetic)
    (dimension : ℕ) : ℤ :=
  data.height (dimension + 1) - data.height dimension

lemma ConwayGuyArithmetic.weights_step (data : ConwayGuyArithmetic)
    (dimension : ℕ) :
    data.weights (dimension + 1) =
      extendWeights (data.head dimension) (data.weights dimension) := by
  funext coordinate
  refine Fin.cases ?_ (fun previous => ?_) coordinate
  · simp [ConwayGuyArithmetic.weights, ConwayGuyArithmetic.head, extendWeights]
  · simp only [ConwayGuyArithmetic.weights, ConwayGuyArithmetic.head,
      extendWeights, Fin.cases_succ]
    have hindex :
        dimension + 1 - (previous.succ.val + 1) =
          dimension - (previous.val + 1) := by
      change dimension + 1 - ((previous.val + 1) + 1) =
        dimension - (previous.val + 1)
      omega
    rw [hindex]
    ring

/-- The exact Conway--Guy-style dimension-lift tower. -/
def ConwayGuyArithmetic.tower (data : ConwayGuyArithmetic) : WeightTower where
  weights := data.weights
  head := data.head
  step := data.weights_step

lemma dot_sub {n : ℕ} (first second weights : Relation n) :
    dot (first - second) weights =
      dot first weights - dot second weights := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

lemma dot_finset_sum {n : ℕ} {α : Type}
    (set : Finset α) (relations : α → Relation n) (weights : Relation n) :
    dot (∑ index ∈ set, relations index) weights =
      ∑ index ∈ set, dot (relations index) weights := by
  classical
  induction set using Finset.induction_on with
  | empty => simp [dot]
  | @insert element set hnotMember inductionHypothesis =>
      simp [hnotMember, dot_add, inductionHypothesis]

lemma principal_dot (offset : ℕ)
    (hblock :
      conwayGuyHeight (offset + 2) -
          ∑ index : Fin (guide (offset + 2)),
            conwayGuyHeight (offset + 2 - index.val - 1) +
        ∑ index : Fin (guide (offset + 2) - 1),
          conwayGuyHeight (triangular index.val) = 1) :
    dot (principal offset) (conwayGuyArithmetic.weights (offset + 2)) = 1 := by
  rw [principal, dot_sub]
  simp only [dot_finset_sum, dot_basis,
    ConwayGuyArithmetic.weights, positiveIndex, negativeIndex]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  push_cast
  have hpositive := guide_pos (dimension := offset + 2) (by omega)
  have hnegativeIndex :
      ∀ index : Fin (guide (offset + 2) - 1),
        offset + 1 -
            (offset + 2 - triangular index.val - 1) =
          triangular index.val := by
    intro index
    have hdeep := correction_deep_bound (dimension := offset + 2)
      (index := index.val) (by omega) index.isLt
    omega
  simp_rw [hnegativeIndex]
  have hpositiveIndex :
      ∀ index : Fin (guide (offset + 2)),
        offset + 2 - index.val - 1 = offset + 1 - index.val := by
    intro index
    omega
  simp_rw [hpositiveIndex] at hblock
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hguide :
      (guide (offset + 2) : ℤ) =
        (guide (offset + 2) - 1 : ℕ) + 1 := by
    omega
  rw [hguide]
  ring_nf
  simpa [conwayGuyArithmetic, Nat.add_comm] using hblock

end BooleanIsoperimetry.CoherentGap
