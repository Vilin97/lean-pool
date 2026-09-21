/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMeasure
import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicCubeTranslation
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeReflection.Reflections
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeReflection.Folding.Geometry

/-! # Block Decomposition -/

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal Topology

noncomputable section

@[simp] theorem cubeCoordinateFoldSign_mul_self {d : ℕ}
    (Q : TriadicCube d) (x : Vec d) (i : Fin d) :
    cubeCoordinateFoldSign Q x i * cubeCoordinateFoldSign Q x i = 1 := by
  by_cases hLower : x i < cubeLowerFaceCoord Q i
  · simp [cubeCoordinateFoldSign, hLower]
  · by_cases hUpper : x i < cubeUpperFaceCoord Q i
    · simp [cubeCoordinateFoldSign, hLower, hUpper]
    · simp [cubeCoordinateFoldSign, hLower, hUpper]

/-- The all-coordinate reflected vector field preserves pointwise Euclidean
self-pairing after folding. -/
theorem vecDot_cubeCoordinateFoldReflectedVectorField_self {d : ℕ}
    (Q : TriadicCube d) (G : Vec d → Vec d) (x : Vec d) :
    vecDot (cubeCoordinateFoldReflectedVectorField Q G x)
      (cubeCoordinateFoldReflectedVectorField Q G x) =
      vecDot (G (cubeCoordinateFold Q x)) (G (cubeCoordinateFold Q x)) := by
  unfold vecDot
  apply Finset.sum_congr rfl
  intro i _hi
  simp [cubeCoordinateFoldReflectedVectorField, mul_left_comm, mul_comm]

/-- The one-coordinate face-neighbor slab is measurable. -/
theorem measurableSet_cubeFaceNeighborSlabSet {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) :
    MeasurableSet (cubeFaceNeighborSlabSet Q i) := by
  exact ((measurableSet_openCubeSet (cubeLowerFaceNeighbor Q i)).union
    (measurableSet_openCubeSet Q)).union
      (measurableSet_openCubeSet (cubeUpperFaceNeighbor Q i))

/-- A one-coordinate reflection-cell strip is measurable. -/
theorem measurableSet_cubeFaceReflectionCellCoordSet {d : ℕ}
    (Q : TriadicCube d) (choice : Fin 3) (i : Fin d) :
    MeasurableSet (cubeFaceReflectionCellCoordSet Q choice i) := by
  classical
  have hLower :
      MeasurableSet
        {x : Vec d |
          cubeLowerFaceCoord Q i - cubeScaleFactor Q < x i ∧
            x i < cubeLowerFaceCoord Q i} := by
    exact (isOpen_lt continuous_const (continuous_apply i)).measurableSet.inter
      (isOpen_lt (continuous_apply i) continuous_const).measurableSet
  have hMiddle :
      MeasurableSet
        {x : Vec d |
          cubeLowerFaceCoord Q i < x i ∧
            x i < cubeUpperFaceCoord Q i} := by
    exact (isOpen_lt continuous_const (continuous_apply i)).measurableSet.inter
      (isOpen_lt (continuous_apply i) continuous_const).measurableSet
  have hUpper :
      MeasurableSet
        {x : Vec d |
          cubeUpperFaceCoord Q i < x i ∧
            x i < cubeUpperFaceCoord Q i + cubeScaleFactor Q} := by
    exact (isOpen_lt continuous_const (continuous_apply i)).measurableSet.inter
      (isOpen_lt (continuous_apply i) continuous_const).measurableSet
  by_cases h0 : choice = 0
  · simpa [cubeFaceReflectionCellCoordSet, h0] using hLower
  · by_cases h1 : choice = 1
    · simpa [cubeFaceReflectionCellCoordSet, h0, h1] using hMiddle
    · simpa [cubeFaceReflectionCellCoordSet, h0, h1] using hUpper

/-- A `3^d` reflection-block cell is measurable. -/
theorem measurableSet_cubeFaceReflectionCellSet {d : ℕ}
    (Q : TriadicCube d) (choice : Fin d → Fin 3) :
    MeasurableSet (cubeFaceReflectionCellSet Q choice) := by
  have h :
      MeasurableSet
        (⋂ i : Fin d, cubeFaceReflectionCellCoordSet Q (choice i) i) :=
    MeasurableSet.iInter fun i : Fin d =>
      measurableSet_cubeFaceReflectionCellCoordSet Q (choice i) i
  convert h using 1
  ext x
  simp [cubeFaceReflectionCellSet]

/-- The all-coordinate reflection block is measurable. -/
theorem measurableSet_cubeFaceReflectionBlockSet {d : ℕ}
    (Q : TriadicCube d) :
    MeasurableSet (cubeFaceReflectionBlockSet Q) := by
  classical
  have hcoord : ∀ i : Fin d,
      MeasurableSet
        {x : Vec d |
          (cubeLowerFaceCoord Q i - cubeScaleFactor Q < x i ∧
            x i < cubeLowerFaceCoord Q i) ∨
          (cubeLowerFaceCoord Q i < x i ∧
            x i < cubeUpperFaceCoord Q i) ∨
          (cubeUpperFaceCoord Q i < x i ∧
            x i < cubeUpperFaceCoord Q i + cubeScaleFactor Q)} := by
    intro i
    have hLower :
        MeasurableSet
          {x : Vec d |
            cubeLowerFaceCoord Q i - cubeScaleFactor Q < x i ∧
              x i < cubeLowerFaceCoord Q i} := by
      exact (isOpen_lt continuous_const (continuous_apply i)).measurableSet.inter
        (isOpen_lt (continuous_apply i) continuous_const).measurableSet
    have hMiddle :
        MeasurableSet
          {x : Vec d |
            cubeLowerFaceCoord Q i < x i ∧
              x i < cubeUpperFaceCoord Q i} := by
      exact (isOpen_lt continuous_const (continuous_apply i)).measurableSet.inter
        (isOpen_lt (continuous_apply i) continuous_const).measurableSet
    have hUpper :
        MeasurableSet
          {x : Vec d |
            cubeUpperFaceCoord Q i < x i ∧
              x i < cubeUpperFaceCoord Q i + cubeScaleFactor Q} := by
      exact (isOpen_lt continuous_const (continuous_apply i)).measurableSet.inter
        (isOpen_lt (continuous_apply i) continuous_const).measurableSet
    simpa [Set.ofPred_or] using hLower.union (hMiddle.union hUpper)
  simpa [cubeFaceReflectionBlockSet, Set.iInter_ofPred] using
    (MeasurableSet.iInter hcoord)

/-- Every reflection-block cell is contained in the full all-coordinate
reflection block. -/
theorem cubeFaceReflectionCellSet_subset_cubeFaceReflectionBlockSet {d : ℕ}
    (Q : TriadicCube d) (choice : Fin d → Fin 3) :
    cubeFaceReflectionCellSet Q choice ⊆ cubeFaceReflectionBlockSet Q := by
  intro x hx i
  have hcoord := hx i
  by_cases h0 : choice i = 0
  · exact Or.inl <| by
      simpa [cubeFaceReflectionCellCoordSet, h0] using hcoord
  · by_cases h1 : choice i = 1
    · exact Or.inr <| Or.inl <| by
        simpa [cubeFaceReflectionCellCoordSet, h0, h1] using hcoord
    · exact Or.inr <| Or.inr <| by
        simpa [cubeFaceReflectionCellCoordSet, h0, h1] using hcoord

/-- The all-coordinate reflection block is the union of its `3^d`
lower/original/upper cells. -/
theorem cubeFaceReflectionBlockSet_eq_iUnion_cellSet {d : ℕ}
    (Q : TriadicCube d) :
    cubeFaceReflectionBlockSet Q =
      ⋃ choice : Fin d → Fin 3, cubeFaceReflectionCellSet Q choice := by
  classical
  ext x
  constructor
  · intro hx
    have hExists :
        ∀ i : Fin d,
          ∃ choice : Fin 3, x ∈ cubeFaceReflectionCellCoordSet Q choice i := by
      intro i
      rcases hx i with hLower | hMiddle | hUpper
      · exact ⟨0, by simpa [cubeFaceReflectionCellCoordSet] using hLower⟩
      · exact ⟨1, by simp [cubeFaceReflectionCellCoordSet, hMiddle]⟩
      · exact ⟨2, by
          have h20 : (2 : Fin 3) ≠ 0 := by decide
          have h21 : (2 : Fin 3) ≠ 1 := by decide
          simpa [cubeFaceReflectionCellCoordSet, h20, h21] using hUpper⟩
    choose choice hchoice using hExists
    exact Set.mem_iUnion.mpr
      ⟨choice, by
        intro i
        exact hchoice i⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨choice, hchoice⟩
    exact cubeFaceReflectionCellSet_subset_cubeFaceReflectionBlockSet Q
      choice hchoice

/-- The all-coordinate reflection block is the union of the translated open
triadic cubes represented by its cells. -/
theorem cubeFaceReflectionBlockSet_eq_iUnion_cellCube {d : ℕ}
    (Q : TriadicCube d) :
    cubeFaceReflectionBlockSet Q =
      ⋃ choice : Fin d → Fin 3,
        openCubeSet (cubeFaceReflectionCellCube Q choice) := by
  simpa [openCubeSet_cubeFaceReflectionCellCube] using
    cubeFaceReflectionBlockSet_eq_iUnion_cellSet Q

/-- Every reflection-block cell is open. -/
theorem isOpen_cubeFaceReflectionCellSet {d : ℕ}
    (Q : TriadicCube d) (choice : Fin d → Fin 3) :
    IsOpen (cubeFaceReflectionCellSet Q choice) := by
  rw [← openCubeSet_cubeFaceReflectionCellCube]
  exact isOpen_openCubeSet (cubeFaceReflectionCellCube Q choice)

/-- The all-coordinate reflection block is open. -/
theorem isOpen_cubeFaceReflectionBlockSet {d : ℕ}
    (Q : TriadicCube d) :
    IsOpen (cubeFaceReflectionBlockSet Q) := by
  rw [cubeFaceReflectionBlockSet_eq_iUnion_cellCube Q]
  exact isOpen_iUnion fun choice : Fin d → Fin 3 =>
    isOpen_openCubeSet (cubeFaceReflectionCellCube Q choice)

/-- Distinct one-coordinate lower/original/upper strips are disjoint. -/
theorem disjoint_cubeFaceReflectionCellCoordSet_of_ne {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) {a b : Fin 3} (hab : a ≠ b) :
    Disjoint (cubeFaceReflectionCellCoordSet Q a i)
      (cubeFaceReflectionCellCoordSet Q b i) := by
  have hscale : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hLowerUpper : cubeLowerFaceCoord Q i < cubeUpperFaceCoord Q i := by
    have hscalePow : 0 < (3 : ℝ) ^ Q.scale := by
      simpa [cubeScaleFactor] using hscale
    dsimp [cubeLowerFaceCoord, cubeUpperFaceCoord, cubeScaleFactor]
    nlinarith
  rw [Set.disjoint_left]
  intro x hxA hxB
  fin_cases a <;> fin_cases b
  · exact (hab rfl).elim
  · have hxA' :
        cubeLowerFaceCoord Q i - cubeScaleFactor Q < x i ∧
          x i < cubeLowerFaceCoord Q i := by
      simpa [cubeFaceReflectionCellCoordSet] using hxA
    have hxB' :
        cubeLowerFaceCoord Q i < x i ∧
          x i < cubeUpperFaceCoord Q i := by
      simp [cubeFaceReflectionCellCoordSet] at hxB
      exact hxB
    linarith
  · have hxA' :
        cubeLowerFaceCoord Q i - cubeScaleFactor Q < x i ∧
          x i < cubeLowerFaceCoord Q i := by
      simpa [cubeFaceReflectionCellCoordSet] using hxA
    have hxB' :
        cubeUpperFaceCoord Q i < x i ∧
          x i < cubeUpperFaceCoord Q i + cubeScaleFactor Q := by
      simp [cubeFaceReflectionCellCoordSet] at hxB
      exact hxB
    linarith
  · have hxA' :
        cubeLowerFaceCoord Q i < x i ∧
          x i < cubeUpperFaceCoord Q i := by
      simp [cubeFaceReflectionCellCoordSet] at hxA
      exact hxA
    have hxB' :
        cubeLowerFaceCoord Q i - cubeScaleFactor Q < x i ∧
          x i < cubeLowerFaceCoord Q i := by
      simpa [cubeFaceReflectionCellCoordSet] using hxB
    linarith
  · exact (hab rfl).elim
  · have hxA' :
        cubeLowerFaceCoord Q i < x i ∧
          x i < cubeUpperFaceCoord Q i := by
      simp [cubeFaceReflectionCellCoordSet] at hxA
      exact hxA
    have hxB' :
        cubeUpperFaceCoord Q i < x i ∧
          x i < cubeUpperFaceCoord Q i + cubeScaleFactor Q := by
      simp [cubeFaceReflectionCellCoordSet] at hxB
      exact hxB
    linarith
  · have hxA' :
        cubeUpperFaceCoord Q i < x i ∧
          x i < cubeUpperFaceCoord Q i + cubeScaleFactor Q := by
      simp [cubeFaceReflectionCellCoordSet] at hxA
      exact hxA
    have hxB' :
        cubeLowerFaceCoord Q i - cubeScaleFactor Q < x i ∧
          x i < cubeLowerFaceCoord Q i := by
      simpa [cubeFaceReflectionCellCoordSet] using hxB
    linarith
  · have hxA' :
        cubeUpperFaceCoord Q i < x i ∧
          x i < cubeUpperFaceCoord Q i + cubeScaleFactor Q := by
      simp [cubeFaceReflectionCellCoordSet] at hxA
      exact hxA
    have hxB' :
        cubeLowerFaceCoord Q i < x i ∧
          x i < cubeUpperFaceCoord Q i := by
      simp [cubeFaceReflectionCellCoordSet] at hxB
      exact hxB
    linarith
  · exact (hab rfl).elim

/-- Different reflection-block cells are disjoint. -/
theorem disjoint_cubeFaceReflectionCellSet_of_ne {d : ℕ}
    (Q : TriadicCube d) {choice₁ choice₂ : Fin d → Fin 3}
    (hchoice : choice₁ ≠ choice₂) :
    Disjoint (cubeFaceReflectionCellSet Q choice₁)
      (cubeFaceReflectionCellSet Q choice₂) := by
  classical
  have hExists : ∃ i : Fin d, choice₁ i ≠ choice₂ i := by
    by_contra hnone
    apply hchoice
    funext i
    by_contra hi
    exact hnone ⟨i, hi⟩
  rcases hExists with ⟨i, hi⟩
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  exact
    (Set.disjoint_left.mp
      (disjoint_cubeFaceReflectionCellCoordSet_of_ne Q i hi)
      (hx₁ i)) (hx₂ i)

/-- The translated open cubes associated to different reflection cells are
disjoint. -/
theorem disjoint_openCubeSet_cubeFaceReflectionCellCube_of_ne {d : ℕ}
    (Q : TriadicCube d) {choice₁ choice₂ : Fin d → Fin 3}
    (hchoice : choice₁ ≠ choice₂) :
    Disjoint (openCubeSet (cubeFaceReflectionCellCube Q choice₁))
      (openCubeSet (cubeFaceReflectionCellCube Q choice₂)) := by
  simpa [openCubeSet_cubeFaceReflectionCellCube] using
    disjoint_cubeFaceReflectionCellSet_of_ne Q hchoice

/-- Set-integral split over the all-coordinate reflection block, written as a
finite sum over its translated open triadic-cube cells. -/
theorem setIntegral_cubeFaceReflectionBlockSet_cellCube {d : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube d) (f : Vec d → E)
    (hf : ∀ choice : Fin d → Fin 3,
      MeasureTheory.Integrable f
        (volume.restrict (openCubeSet (cubeFaceReflectionCellCube Q choice)))) :
    ∫ x in cubeFaceReflectionBlockSet Q, f x ∂volume =
      ∑ choice : Fin d → Fin 3,
        ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
          f x ∂volume := by
  rw [cubeFaceReflectionBlockSet_eq_iUnion_cellCube Q]
  exact MeasureTheory.integral_iUnion_fintype
    (μ := volume)
    (s := fun choice : Fin d → Fin 3 =>
      openCubeSet (cubeFaceReflectionCellCube Q choice))
    (f := f)
    (fun choice =>
      measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice))
    (by
      intro choice₁ choice₂ hne
      exact disjoint_openCubeSet_cubeFaceReflectionCellCube_of_ne Q hne)
    (fun choice => by
      simpa [MeasureTheory.IntegrableOn] using hf choice)

/-- The reflection block has one lower/original/upper choice in each
coordinate, hence `3^d` cells. -/
theorem card_cubeFaceReflectionChoices (d : ℕ) :
    Fintype.card (Fin d → Fin 3) = 3 ^ d := by
  simp

/-- Real-valued form of `card_cubeFaceReflectionChoices`, for constants in
energy estimates. -/
theorem real_card_cubeFaceReflectionChoices (d : ℕ) :
    (Fintype.card (Fin d → Fin 3) : ℝ) = (3 : ℝ) ^ d := by
  norm_num [card_cubeFaceReflectionChoices]

/-- The original open cube is contained in the all-coordinate reflection
block. -/
theorem openCubeSet_subset_cubeFaceReflectionBlockSet {d : ℕ}
    (Q : TriadicCube d) :
    openCubeSet Q ⊆ cubeFaceReflectionBlockSet Q := by
  intro x hx j
  exact Or.inr <| Or.inl
    ⟨by simpa [cubeLowerFaceCoord] using (hx j).1,
      by simpa [cubeUpperFaceCoord] using (hx j).2⟩

/-- A lower same-scale face neighbor is contained in the all-coordinate
reflection block. -/
theorem openCubeSet_cubeLowerFaceNeighbor_subset_cubeFaceReflectionBlockSet
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) :
    openCubeSet (cubeLowerFaceNeighbor Q i) ⊆
      cubeFaceReflectionBlockSet Q := by
  intro x hx j
  by_cases hji : j = i
  · subst j
    exact Or.inl
      ⟨by
          have hLower :
              cubeLowerFaceCoord (cubeLowerFaceNeighbor Q i) i < x i := by
            simpa [cubeLowerFaceCoord] using (hx i).1
          simpa using hLower,
        by
          have hUpper :
              x i < cubeUpperFaceCoord (cubeLowerFaceNeighbor Q i) i := by
            simpa [cubeUpperFaceCoord] using (hx i).2
          simpa using hUpper⟩
  · exact Or.inr <| Or.inl
      ⟨by
          have hLower :
              cubeLowerFaceCoord (cubeLowerFaceNeighbor Q i) j < x j := by
            simpa [cubeLowerFaceCoord] using (hx j).1
          simpa [hji] using hLower,
        by
          have hUpper :
              x j < cubeUpperFaceCoord (cubeLowerFaceNeighbor Q i) j := by
            simpa [cubeUpperFaceCoord] using (hx j).2
          simpa [hji] using hUpper⟩

/-- An upper same-scale face neighbor is contained in the all-coordinate
reflection block. -/
theorem openCubeSet_cubeUpperFaceNeighbor_subset_cubeFaceReflectionBlockSet
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) :
    openCubeSet (cubeUpperFaceNeighbor Q i) ⊆
      cubeFaceReflectionBlockSet Q := by
  intro x hx j
  by_cases hji : j = i
  · subst j
    exact Or.inr <| Or.inr
      ⟨by
          have hLower :
              cubeLowerFaceCoord (cubeUpperFaceNeighbor Q i) i < x i := by
            simpa [cubeLowerFaceCoord] using (hx i).1
          simpa using hLower,
        by
          have hUpper :
              x i < cubeUpperFaceCoord (cubeUpperFaceNeighbor Q i) i := by
            simpa [cubeUpperFaceCoord] using (hx i).2
          simpa using hUpper⟩
  · exact Or.inr <| Or.inl
      ⟨by
          have hLower :
              cubeLowerFaceCoord (cubeUpperFaceNeighbor Q i) j < x j := by
            simpa [cubeLowerFaceCoord] using (hx j).1
          simpa [hji] using hLower,
        by
          have hUpper :
              x j < cubeUpperFaceCoord (cubeUpperFaceNeighbor Q i) j := by
            simpa [cubeUpperFaceCoord] using (hx j).2
          simpa [hji] using hUpper⟩

/-- Every one-coordinate lower/original/upper slab is contained in the
all-coordinate reflection block. -/
theorem cubeFaceNeighborSlabSet_subset_cubeFaceReflectionBlockSet
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) :
    cubeFaceNeighborSlabSet Q i ⊆ cubeFaceReflectionBlockSet Q := by
  intro x hx
  rcases hx with hxLQ | hxU
  · rcases hxLQ with hxL | hxQ
    · exact openCubeSet_cubeLowerFaceNeighbor_subset_cubeFaceReflectionBlockSet
        Q i hxL
    · exact openCubeSet_subset_cubeFaceReflectionBlockSet Q hxQ
  · exact openCubeSet_cubeUpperFaceNeighbor_subset_cubeFaceReflectionBlockSet
      Q i hxU

/-- On the original open cube, the coordinatewise fold is the identity. -/
theorem cubeCoordinateFold_eq_self_of_mem_openCubeSet {d : ℕ}
    (Q : TriadicCube d) {x : Vec d} (hx : x ∈ openCubeSet Q) :
    cubeCoordinateFold Q x = x := by
  ext i
  have hLower : cubeLowerFaceCoord Q i < x i := by
    simpa [cubeLowerFaceCoord] using (hx i).1
  have hUpper : x i < cubeUpperFaceCoord Q i := by
    simpa [cubeUpperFaceCoord] using (hx i).2
  have hnotLower : ¬ x i < cubeLowerFaceCoord Q i := not_lt.mpr hLower.le
  simp [cubeCoordinateFold, hnotLower, hUpper]

theorem cubeCoordinateFoldReflectedScalar_eq_self_of_mem_openCubeSet {d : ℕ}
    (Q : TriadicCube d) (F : Vec d → ℝ) {x : Vec d}
    (hx : x ∈ openCubeSet Q) :
    cubeCoordinateFoldReflectedScalar Q F x = F x := by
  simp [cubeCoordinateFoldReflectedScalar,
    cubeCoordinateFold_eq_self_of_mem_openCubeSet Q hx]

theorem cubeCoordinateFoldReflectedVectorField_eq_self_of_mem_openCubeSet {d : ℕ}
    (Q : TriadicCube d) (G : Vec d → Vec d) {x : Vec d}
    (hx : x ∈ openCubeSet Q) :
    cubeCoordinateFoldReflectedVectorField Q G x = G x := by
  ext i
  have hLower : cubeLowerFaceCoord Q i < x i := by
    simpa [cubeLowerFaceCoord] using (hx i).1
  have hUpper : x i < cubeUpperFaceCoord Q i := by
    simpa [cubeUpperFaceCoord] using (hx i).2
  have hnotLower : ¬ x i < cubeLowerFaceCoord Q i := not_lt.mpr hLower.le
  simp [cubeCoordinateFoldReflectedVectorField, cubeCoordinateFoldSign,
    cubeCoordinateFold_eq_self_of_mem_openCubeSet Q hx, hnotLower, hUpper]

/-- On the lower same-scale face neighbor, the all-coordinate fold is the
one-coordinate lower-face reflection. -/
theorem cubeCoordinateFold_eq_cubeLowerFaceReflection_of_mem_neighbor {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) {x : Vec d}
    (hx : x ∈ openCubeSet (cubeLowerFaceNeighbor Q i)) :
    cubeCoordinateFold Q x = cubeLowerFaceReflection Q i x := by
  ext j
  by_cases hji : j = i
  · subst j
    have hLower : x i < cubeLowerFaceCoord Q i := by
      have hxi := (hx i).2
      simp [cubeLowerFaceNeighbor, coordIndexShift,
        translateCube, cubeScaleFactor] at hxi
      have hface :
          (↑(Q.index i) + -1 + (2 : ℝ)⁻¹) * 3 ^ Q.scale =
            cubeLowerFaceCoord Q i := by
        simp [cubeLowerFaceCoord, cubeScaleFactor]
        ring_nf
        left
        trivial
      rwa [hface] at hxi
    simp [cubeCoordinateFold, cubeLowerFaceReflection, hLower]
  · have hxjQ :
        cubeLowerFaceCoord Q j < x j ∧ x j < cubeUpperFaceCoord Q j := by
      have hxj := hx j
      simpa [openCubeSet, cubeLowerFaceNeighbor, coordIndexShift,
        translateCube, cubeLowerFaceCoord, cubeUpperFaceCoord, hji] using! hxj
    have hnotLower : ¬ x j < cubeLowerFaceCoord Q j :=
      not_lt.mpr hxjQ.1.le
    simp [cubeCoordinateFold, cubeLowerFaceReflection, hji, hnotLower,
      hxjQ.2]

/-- On the upper same-scale face neighbor, the all-coordinate fold is the
one-coordinate upper-face reflection. -/
theorem cubeCoordinateFold_eq_cubeUpperFaceReflection_of_mem_neighbor {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) {x : Vec d}
    (hx : x ∈ openCubeSet (cubeUpperFaceNeighbor Q i)) :
    cubeCoordinateFold Q x = cubeUpperFaceReflection Q i x := by
  ext j
  by_cases hji : j = i
  · subst j
    have hnotLower : ¬ x i < cubeLowerFaceCoord Q i := by
      have hxi := (hx i).1
      have hscale : 0 < (3 : ℝ) ^ Q.scale := by
        simpa [cubeScaleFactor] using
          (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
      simp [cubeUpperFaceNeighbor, coordIndexShift, translateCube,
        cubeScaleFactor] at hxi
      have hface :
          (↑(Q.index i) + 1 - (2 : ℝ)⁻¹) * 3 ^ Q.scale =
            cubeUpperFaceCoord Q i := by
        simp [cubeUpperFaceCoord, cubeScaleFactor]
        ring_nf
        left
        trivial
      rw [hface] at hxi
      have hLowerUpper :
          cubeLowerFaceCoord Q i < cubeUpperFaceCoord Q i := by
        dsimp [cubeLowerFaceCoord, cubeUpperFaceCoord, cubeScaleFactor]
        nlinarith
      rw [not_lt]
      exact le_trans hLowerUpper.le hxi.le
    have hnotUpper : ¬ x i < cubeUpperFaceCoord Q i := by
      have hxi := (hx i).1
      simp [cubeUpperFaceNeighbor, coordIndexShift, translateCube,
        cubeScaleFactor] at hxi
      have hface :
          (↑(Q.index i) + 1 - (2 : ℝ)⁻¹) * 3 ^ Q.scale =
            cubeUpperFaceCoord Q i := by
        simp [cubeUpperFaceCoord, cubeScaleFactor]
        ring_nf
        left
        trivial
      rw [hface] at hxi
      exact not_lt.mpr hxi.le
    simp [cubeCoordinateFold, cubeUpperFaceReflection, hnotLower, hnotUpper]
  · have hxjQ :
        cubeLowerFaceCoord Q j < x j ∧ x j < cubeUpperFaceCoord Q j := by
      have hxj := hx j
      simpa [openCubeSet, cubeUpperFaceNeighbor, coordIndexShift,
        translateCube, cubeLowerFaceCoord, cubeUpperFaceCoord, hji] using! hxj
    have hnotLower : ¬ x j < cubeLowerFaceCoord Q j :=
      not_lt.mpr hxjQ.1.le
    simp [cubeCoordinateFold, cubeUpperFaceReflection, hji, hnotLower,
      hxjQ.2]

/-- The all-coordinate fold sign is `1` on the original open cube. -/
theorem cubeCoordinateFoldSign_eq_one_of_mem_openCubeSet {d : ℕ}
    (Q : TriadicCube d) {x : Vec d} (hx : x ∈ openCubeSet Q)
    (i : Fin d) :
    cubeCoordinateFoldSign Q x i = 1 := by
  have hLower : cubeLowerFaceCoord Q i < x i := by
    simpa [cubeLowerFaceCoord] using (hx i).1
  have hUpper : x i < cubeUpperFaceCoord Q i := by
    simpa [cubeUpperFaceCoord] using (hx i).2
  have hnotLower : ¬ x i < cubeLowerFaceCoord Q i := not_lt.mpr hLower.le
  simp [cubeCoordinateFoldSign, hnotLower, hUpper]

/-- On the lower same-scale face neighbor, the all-coordinate fold sign is the
one-coordinate reflection sign. -/
theorem cubeCoordinateFoldSign_of_mem_cubeLowerFaceNeighbor {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) {x : Vec d}
    (hx : x ∈ openCubeSet (cubeLowerFaceNeighbor Q i)) (j : Fin d) :
    cubeCoordinateFoldSign Q x j = if j = i then -1 else 1 := by
  by_cases hji : j = i
  · subst j
    have hLower : x i < cubeLowerFaceCoord Q i := by
      have hxi := (hx i).2
      simp [cubeLowerFaceNeighbor, coordIndexShift,
        translateCube, cubeScaleFactor] at hxi
      have hface :
          (↑(Q.index i) + -1 + (2 : ℝ)⁻¹) * 3 ^ Q.scale =
            cubeLowerFaceCoord Q i := by
        simp [cubeLowerFaceCoord, cubeScaleFactor]
        ring_nf
        left
        trivial
      rwa [hface] at hxi
    simp [cubeCoordinateFoldSign, hLower]
  · have hxjQ :
        cubeLowerFaceCoord Q j < x j ∧ x j < cubeUpperFaceCoord Q j := by
      have hxj := hx j
      simpa [openCubeSet, cubeLowerFaceNeighbor, coordIndexShift,
        translateCube, cubeLowerFaceCoord, cubeUpperFaceCoord, hji] using! hxj
    have hnotLower : ¬ x j < cubeLowerFaceCoord Q j :=
      not_lt.mpr hxjQ.1.le
    simp [cubeCoordinateFoldSign, hji, hnotLower, hxjQ.2]

/-- On the upper same-scale face neighbor, the all-coordinate fold sign is the
one-coordinate reflection sign. -/
theorem cubeCoordinateFoldSign_of_mem_cubeUpperFaceNeighbor {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) {x : Vec d}
    (hx : x ∈ openCubeSet (cubeUpperFaceNeighbor Q i)) (j : Fin d) :
    cubeCoordinateFoldSign Q x j = if j = i then -1 else 1 := by
  by_cases hji : j = i
  · subst j
    have hnotLower : ¬ x i < cubeLowerFaceCoord Q i := by
      have hxi := (hx i).1
      have hscale : 0 < (3 : ℝ) ^ Q.scale := by
        simpa [cubeScaleFactor] using
          (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
      simp [cubeUpperFaceNeighbor, coordIndexShift, translateCube,
        cubeScaleFactor] at hxi
      have hface :
          (↑(Q.index i) + 1 - (2 : ℝ)⁻¹) * 3 ^ Q.scale =
            cubeUpperFaceCoord Q i := by
        simp [cubeUpperFaceCoord, cubeScaleFactor]
        ring_nf
        left
        trivial
      rw [hface] at hxi
      have hLowerUpper :
          cubeLowerFaceCoord Q i < cubeUpperFaceCoord Q i := by
        dsimp [cubeLowerFaceCoord, cubeUpperFaceCoord, cubeScaleFactor]
        nlinarith
      rw [not_lt]
      exact le_trans hLowerUpper.le hxi.le
    have hnotUpper : ¬ x i < cubeUpperFaceCoord Q i := by
      have hxi := (hx i).1
      simp [cubeUpperFaceNeighbor, coordIndexShift, translateCube,
        cubeScaleFactor] at hxi
      have hface :
          (↑(Q.index i) + 1 - (2 : ℝ)⁻¹) * 3 ^ Q.scale =
            cubeUpperFaceCoord Q i := by
        simp [cubeUpperFaceCoord, cubeScaleFactor]
        ring_nf
        left
        trivial
      rw [hface] at hxi
      exact not_lt.mpr hxi.le
    simp [cubeCoordinateFoldSign, hnotLower, hnotUpper]
  · have hxjQ :
        cubeLowerFaceCoord Q j < x j ∧ x j < cubeUpperFaceCoord Q j := by
      have hxj := hx j
      simpa [openCubeSet, cubeUpperFaceNeighbor, coordIndexShift,
        translateCube, cubeLowerFaceCoord, cubeUpperFaceCoord, hji] using! hxj
    have hnotLower : ¬ x j < cubeLowerFaceCoord Q j :=
      not_lt.mpr hxjQ.1.le
    simp [cubeCoordinateFoldSign, hji, hnotLower, hxjQ.2]

/-- The coordinatewise fold maps the open all-coordinate reflection block into
the original open cube. -/
theorem cubeCoordinateFold_mem_openCubeSet_of_mem_block {d : ℕ}
    (Q : TriadicCube d) {x : Vec d}
    (hx : x ∈ cubeFaceReflectionBlockSet Q) :
    cubeCoordinateFold Q x ∈ openCubeSet Q := by
  intro i
  let l := cubeLowerFaceCoord Q i
  let u := cubeUpperFaceCoord Q i
  let s := cubeScaleFactor Q
  have hs : 0 < s := by
    simpa [s, cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hus : u - l = s := by
    dsimp [u, l, s, cubeUpperFaceCoord, cubeLowerFaceCoord]
    ring
  rcases hx i with hLower | hMiddle | hUpper
  · have hfold :
        cubeCoordinateFold Q x i = 2 * l - x i := by
      simp [cubeCoordinateFold, l, hLower.2]
    constructor
    · change l < cubeCoordinateFold Q x i
      rw [hfold]
      linarith
    · change cubeCoordinateFold Q x i < u
      rw [hfold]
      linarith
  · have hnotLower : ¬ x i < l := not_lt.mpr hMiddle.1.le
    have hfold : cubeCoordinateFold Q x i = x i := by
      simp [cubeCoordinateFold, l, hnotLower, hMiddle.2]
    constructor
    · change l < cubeCoordinateFold Q x i
      rw [hfold]
      exact hMiddle.1
    · change cubeCoordinateFold Q x i < u
      rw [hfold]
      exact hMiddle.2
  · have hnotLower : ¬ x i < l := by
      exact not_lt.mpr (le_trans (by linarith [hus, hs]) hUpper.1.le)
    have hnotUpper : ¬ x i < u := not_lt.mpr hUpper.1.le
    have hfold :
        cubeCoordinateFold Q x i = 2 * u - x i := by
      simp [cubeCoordinateFold, l, u, hnotLower, hnotUpper]
    constructor
    · change l < cubeCoordinateFold Q x i
      rw [hfold]
      linarith
    · change cubeCoordinateFold Q x i < u
      rw [hfold]
      linarith

/-- On each reflection-block cell, the `x`-dependent coordinate fold agrees
with the affine fold map attached to that cell. -/
theorem cubeCoordinateFold_eq_cubeFaceReflectionCellFoldMap_of_mem_cellCube
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    {x : Vec d}
    (hx : x ∈ openCubeSet (cubeFaceReflectionCellCube Q choice)) :
    cubeCoordinateFold Q x = cubeFaceReflectionCellFoldMap Q choice x := by
  have hxCell : x ∈ cubeFaceReflectionCellSet Q choice := by
    simpa [openCubeSet_cubeFaceReflectionCellCube] using hx
  ext i
  let l := cubeLowerFaceCoord Q i
  let u := cubeUpperFaceCoord Q i
  let s := cubeScaleFactor Q
  have hu : u = l + s := by
    dsimp [u, l, s, cubeUpperFaceCoord, cubeLowerFaceCoord,
      cubeScaleFactor]
    ring
  have hs : 0 < s := by
    simpa [s, cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hlu : l < u := by
    rw [hu]
    exact lt_add_of_pos_right l hs
  have hcoord := hxCell i
  by_cases h0 : choice i = 0
  · have hstrip : l - s < x i ∧ x i < l := by
      simpa [cubeFaceReflectionCellCoordSet, h0, l, s] using hcoord
    have hLower : x i < cubeLowerFaceCoord Q i := by
      simpa [l] using hstrip.2
    simp [cubeCoordinateFold, cubeFaceReflectionCellFoldMap, h0, hLower]
  · by_cases h1 : choice i = 1
    · have hstrip : l < x i ∧ x i < u := by
        simpa [cubeFaceReflectionCellCoordSet, h0, h1, l, u] using
          hcoord
      have hnotLower : ¬ x i < cubeLowerFaceCoord Q i := by
        simpa [l] using not_lt.mpr hstrip.1.le
      have hUpper : x i < cubeUpperFaceCoord Q i := by
        simpa [u] using hstrip.2
      simp [cubeCoordinateFold, cubeFaceReflectionCellFoldMap, h1,
        hnotLower, hUpper]
    · have hstrip : u < x i ∧ x i < u + s := by
        simpa [cubeFaceReflectionCellCoordSet, h0, h1, u, s] using
          hcoord
      have hli : cubeLowerFaceCoord Q i < x i := by
        have hliu : l < x i := lt_trans hlu hstrip.1
        simpa [l] using hliu
      have hnotLower : ¬ x i < cubeLowerFaceCoord Q i :=
        not_lt.mpr hli.le
      have hnotUpper : ¬ x i < cubeUpperFaceCoord Q i := by
        simpa [u] using not_lt.mpr hstrip.1.le
      simp [cubeCoordinateFold, cubeFaceReflectionCellFoldMap, h0, h1,
        hnotLower, hnotUpper]

/-- On each reflection-block cell, the `x`-dependent fold sign is the
constant sign of the affine cell fold. -/
theorem cubeCoordinateFoldSign_eq_cellFoldLinear_sign_of_mem_cellCube
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    {x : Vec d}
    (hx : x ∈ openCubeSet (cubeFaceReflectionCellCube Q choice))
    (i : Fin d) :
    cubeCoordinateFoldSign Q x i = if choice i = 1 then 1 else -1 := by
  have hxCell : x ∈ cubeFaceReflectionCellSet Q choice := by
    simpa [openCubeSet_cubeFaceReflectionCellCube] using hx
  let l := cubeLowerFaceCoord Q i
  let u := cubeUpperFaceCoord Q i
  let s := cubeScaleFactor Q
  have hcoord := hxCell i
  by_cases h0 : choice i = 0
  · have hstrip : l - s < x i ∧ x i < l := by
      simpa [cubeFaceReflectionCellCoordSet, h0, l, s] using hcoord
    have hLower : x i < cubeLowerFaceCoord Q i := by
      simpa [l] using hstrip.2
    simp [cubeCoordinateFoldSign, h0, hLower]
  · by_cases h1 : choice i = 1
    · have hstrip : l < x i ∧ x i < u := by
        simpa [cubeFaceReflectionCellCoordSet, h0, h1, l, u] using
          hcoord
      have hnotLower : ¬ x i < cubeLowerFaceCoord Q i := by
        simpa [l] using not_lt.mpr hstrip.1.le
      have hUpper : x i < cubeUpperFaceCoord Q i := by
        simpa [u] using hstrip.2
      simp [cubeCoordinateFoldSign, h1, hnotLower, hUpper]
    · have hstrip : u < x i ∧ x i < u + s := by
        simpa [cubeFaceReflectionCellCoordSet, h0, h1, u, s] using
          hcoord
      have hnotLower : ¬ x i < cubeLowerFaceCoord Q i := by
        have hscale : 0 < s := by
          simpa [s, cubeScaleFactor] using
            (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
        have hlu : l < u := by
          dsimp [l, u, s, cubeLowerFaceCoord, cubeUpperFaceCoord,
            cubeScaleFactor] at hscale ⊢
          nlinarith
        exact not_lt.mpr (le_trans hlu.le (by simpa [u] using hstrip.1.le))
      have hnotUpper : ¬ x i < cubeUpperFaceCoord Q i := by
        simpa [u] using not_lt.mpr hstrip.1.le
      simp [cubeCoordinateFoldSign, h1, hnotLower, hnotUpper]

/-- On each reflection-block cell, scalar pullback by the `x`-dependent fold
agrees with scalar pullback by the affine cell fold. -/
theorem cubeCoordinateFoldReflectedScalar_eq_cellFoldMap_of_mem_cellCube
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    (F : Vec d → ℝ) {x : Vec d}
    (hx : x ∈ openCubeSet (cubeFaceReflectionCellCube Q choice)) :
    cubeCoordinateFoldReflectedScalar Q F x =
      F (cubeFaceReflectionCellFoldMap Q choice x) := by
  simp [cubeCoordinateFoldReflectedScalar,
    cubeCoordinateFold_eq_cubeFaceReflectionCellFoldMap_of_mem_cellCube
      Q choice hx]

/-- On each reflection-block cell, the reflected vector field agrees with the
affine cell-fold linear sign applied to the pulled-back vector field. -/
theorem cubeCoordinateFoldReflectedVectorField_eq_cellFoldLinear_of_mem_cellCube
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    (G : Vec d → Vec d) {x : Vec d}
    (hx : x ∈ openCubeSet (cubeFaceReflectionCellCube Q choice)) :
    cubeCoordinateFoldReflectedVectorField Q G x =
      cubeFaceReflectionCellFoldLinear choice
        (G (cubeFaceReflectionCellFoldMap Q choice x)) := by
  ext i
  rw [cubeCoordinateFoldReflectedVectorField,
    cubeCoordinateFold_eq_cubeFaceReflectionCellFoldMap_of_mem_cellCube
      Q choice hx]
  rw [cubeCoordinateFoldSign_eq_cellFoldLinear_sign_of_mem_cellCube
    Q choice hx i]
  by_cases h1 : choice i = 1 <;> simp [h1]

end

end Homogenization
