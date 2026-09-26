/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMeasure
public import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicCubeTranslation
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeReflection.Reflections

/-! # Geometry -/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal Topology

noncomputable section

/-- The three-cube slab obtained by adjoining both same-coordinate face
neighbors to `Q`. -/
def cubeFaceNeighborSlabSet {d : ℕ} (Q : TriadicCube d) (i : Fin d) :
    Set (Vec d) :=
  (openCubeSet (cubeLowerFaceNeighbor Q i) ∪ openCubeSet Q) ∪
    openCubeSet (cubeUpperFaceNeighbor Q i)

/-- The open block obtained by allowing each coordinate to lie in the lower
neighbor strip, the original cube strip, or the upper neighbor strip.

This is the all-coordinate target for iterating the one-coordinate reflection
argument. It excludes the internal reflecting faces, which are null sets for
the later weak-form argument. -/
def cubeFaceReflectionBlockSet {d : ℕ} (Q : TriadicCube d) :
    Set (Vec d) :=
  {x | ∀ i : Fin d,
    (cubeLowerFaceCoord Q i - cubeScaleFactor Q < x i ∧
      x i < cubeLowerFaceCoord Q i) ∨
    (cubeLowerFaceCoord Q i < x i ∧
      x i < cubeUpperFaceCoord Q i) ∨
    (cubeUpperFaceCoord Q i < x i ∧
      x i < cubeUpperFaceCoord Q i + cubeScaleFactor Q)}

/-- One coordinate strip of the all-coordinate reflection block. The choice
`0` is the lower neighbor strip, `1` is the original cube strip, and `2` is the
upper neighbor strip. -/
def cubeFaceReflectionCellCoordSet {d : ℕ}
    (Q : TriadicCube d) (choice : Fin 3) (i : Fin d) :
    Set (Vec d) :=
  if choice = 0 then
    {x | cubeLowerFaceCoord Q i - cubeScaleFactor Q < x i ∧
      x i < cubeLowerFaceCoord Q i}
  else if choice = 1 then
    {x | cubeLowerFaceCoord Q i < x i ∧
      x i < cubeUpperFaceCoord Q i}
  else
    {x | cubeUpperFaceCoord Q i < x i ∧
      x i < cubeUpperFaceCoord Q i + cubeScaleFactor Q}

/-- A `3^d` cell of the all-coordinate reflection block, with an independent
lower/original/upper strip choice in every coordinate. -/
def cubeFaceReflectionCellSet {d : ℕ}
    (Q : TriadicCube d) (choice : Fin d → Fin 3) : Set (Vec d) :=
  {x | ∀ i : Fin d, x ∈ cubeFaceReflectionCellCoordSet Q (choice i) i}

/-- Integer shift associated to a reflection cell coordinate choice:
lower/original/upper corresponds to `-1/0/1`. -/
def cubeFaceReflectionCellShift (choice : Fin 3) : ℤ :=
  if choice = 0 then -1 else if choice = 1 then 0 else 1

/-- The translated cube represented by a `3^d` reflection-block cell. -/
def cubeFaceReflectionCellCube {d : ℕ}
    (Q : TriadicCube d) (choice : Fin d → Fin 3) : TriadicCube d :=
  translateCube (fun i => cubeFaceReflectionCellShift (choice i)) Q

theorem cubeLowerFaceCoord_cubeFaceReflectionCellCube_of_choice_eq_zero
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    {i : Fin d} (h0 : choice i = 0) :
    cubeLowerFaceCoord (cubeFaceReflectionCellCube Q choice) i =
      cubeLowerFaceCoord Q i - cubeScaleFactor Q := by
  simp [cubeFaceReflectionCellCube, cubeFaceReflectionCellShift,
    cubeLowerFaceCoord, translateCube, cubeScaleFactor, h0]
  ring_nf

theorem cubeUpperFaceCoord_cubeFaceReflectionCellCube_of_choice_eq_zero
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    {i : Fin d} (h0 : choice i = 0) :
    cubeUpperFaceCoord (cubeFaceReflectionCellCube Q choice) i =
      cubeLowerFaceCoord Q i := by
  simp [cubeFaceReflectionCellCube, cubeFaceReflectionCellShift,
    cubeUpperFaceCoord, cubeLowerFaceCoord, translateCube, cubeScaleFactor,
    h0]
  ring_nf
  left
  trivial

theorem cubeLowerFaceCoord_cubeFaceReflectionCellCube_of_choice_eq_one
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    {i : Fin d} (h1 : choice i = 1) :
    cubeLowerFaceCoord (cubeFaceReflectionCellCube Q choice) i =
      cubeLowerFaceCoord Q i := by
  simp [cubeFaceReflectionCellCube, cubeFaceReflectionCellShift,
    cubeLowerFaceCoord, translateCube, cubeScaleFactor, h1]

theorem cubeUpperFaceCoord_cubeFaceReflectionCellCube_of_choice_eq_one
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    {i : Fin d} (h1 : choice i = 1) :
    cubeUpperFaceCoord (cubeFaceReflectionCellCube Q choice) i =
      cubeUpperFaceCoord Q i := by
  simp [cubeFaceReflectionCellCube, cubeFaceReflectionCellShift,
    cubeUpperFaceCoord, translateCube, cubeScaleFactor, h1]

theorem cubeLowerFaceCoord_cubeFaceReflectionCellCube_of_choice_upper
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    {i : Fin d} (h0 : choice i ≠ 0) (h1 : choice i ≠ 1) :
    cubeLowerFaceCoord (cubeFaceReflectionCellCube Q choice) i =
      cubeUpperFaceCoord Q i := by
  simp [cubeFaceReflectionCellCube, cubeFaceReflectionCellShift,
    cubeLowerFaceCoord, cubeUpperFaceCoord, translateCube, cubeScaleFactor,
    h0, h1]
  ring_nf
  left
  trivial

theorem cubeUpperFaceCoord_cubeFaceReflectionCellCube_of_choice_upper
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    {i : Fin d} (h0 : choice i ≠ 0) (h1 : choice i ≠ 1) :
    cubeUpperFaceCoord (cubeFaceReflectionCellCube Q choice) i =
      cubeUpperFaceCoord Q i + cubeScaleFactor Q := by
  simp [cubeFaceReflectionCellCube, cubeFaceReflectionCellShift,
    cubeUpperFaceCoord, translateCube, cubeScaleFactor, h0, h1]
  ring_nf

/-- A reflection-block cell is exactly the open translated triadic cube with
coordinate shifts `-1/0/1` prescribed by its choices. -/
theorem openCubeSet_cubeFaceReflectionCellCube {d : ℕ}
    (Q : TriadicCube d) (choice : Fin d → Fin 3) :
    openCubeSet (cubeFaceReflectionCellCube Q choice) =
      cubeFaceReflectionCellSet Q choice := by
  ext x
  constructor
  · intro hx i
    have hLowerCell :
        cubeLowerFaceCoord (cubeFaceReflectionCellCube Q choice) i < x i := by
      simpa [cubeLowerFaceCoord] using (hx i).1
    have hUpperCell :
        x i < cubeUpperFaceCoord (cubeFaceReflectionCellCube Q choice) i := by
      simpa [cubeUpperFaceCoord] using (hx i).2
    by_cases h0 : choice i = 0
    · have hLower :
          cubeLowerFaceCoord Q i - cubeScaleFactor Q < x i := by
        simpa [cubeLowerFaceCoord_cubeFaceReflectionCellCube_of_choice_eq_zero
          Q choice h0] using hLowerCell
      have hUpper : x i < cubeLowerFaceCoord Q i := by
        simpa [cubeUpperFaceCoord_cubeFaceReflectionCellCube_of_choice_eq_zero
          Q choice h0] using hUpperCell
      simpa [cubeFaceReflectionCellCoordSet, h0] using
        (And.intro hLower hUpper)
    · by_cases h1 : choice i = 1
      · have hLower : cubeLowerFaceCoord Q i < x i := by
          simpa [cubeLowerFaceCoord_cubeFaceReflectionCellCube_of_choice_eq_one
            Q choice h1] using hLowerCell
        have hUpper : x i < cubeUpperFaceCoord Q i := by
          simpa [cubeUpperFaceCoord_cubeFaceReflectionCellCube_of_choice_eq_one
            Q choice h1] using hUpperCell
        simpa [cubeFaceReflectionCellCoordSet, h0, h1] using
          (And.intro hLower hUpper)
      · have hLower : cubeUpperFaceCoord Q i < x i := by
          simpa [cubeLowerFaceCoord_cubeFaceReflectionCellCube_of_choice_upper
            Q choice h0 h1] using hLowerCell
        have hUpper :
            x i < cubeUpperFaceCoord Q i + cubeScaleFactor Q := by
          simpa [cubeUpperFaceCoord_cubeFaceReflectionCellCube_of_choice_upper
            Q choice h0 h1] using hUpperCell
        simpa [cubeFaceReflectionCellCoordSet, h0, h1] using
          (And.intro hLower hUpper)
  · intro hx i
    have hcoord := hx i
    by_cases h0 : choice i = 0
    · have hstrip :
          cubeLowerFaceCoord Q i - cubeScaleFactor Q < x i ∧
            x i < cubeLowerFaceCoord Q i := by
        simpa [cubeFaceReflectionCellCoordSet, h0] using hcoord
      constructor
      · have hLowerCell :
            cubeLowerFaceCoord (cubeFaceReflectionCellCube Q choice) i < x i := by
          simpa [cubeLowerFaceCoord_cubeFaceReflectionCellCube_of_choice_eq_zero
            Q choice h0] using hstrip.1
        simpa [cubeLowerFaceCoord] using hLowerCell
      · have hUpperCell :
            x i < cubeUpperFaceCoord (cubeFaceReflectionCellCube Q choice) i := by
          simpa [cubeUpperFaceCoord_cubeFaceReflectionCellCube_of_choice_eq_zero
            Q choice h0] using hstrip.2
        simpa [cubeUpperFaceCoord] using hUpperCell
    · by_cases h1 : choice i = 1
      · have hstrip :
            cubeLowerFaceCoord Q i < x i ∧
              x i < cubeUpperFaceCoord Q i := by
          simpa [cubeFaceReflectionCellCoordSet, h0, h1] using hcoord
        constructor
        · have hLowerCell :
              cubeLowerFaceCoord (cubeFaceReflectionCellCube Q choice) i < x i := by
            simpa [cubeLowerFaceCoord_cubeFaceReflectionCellCube_of_choice_eq_one
              Q choice h1] using hstrip.1
          simpa [cubeLowerFaceCoord] using hLowerCell
        · have hUpperCell :
              x i < cubeUpperFaceCoord (cubeFaceReflectionCellCube Q choice) i := by
            simpa [cubeUpperFaceCoord_cubeFaceReflectionCellCube_of_choice_eq_one
              Q choice h1] using hstrip.2
          simpa [cubeUpperFaceCoord] using hUpperCell
      · have hstrip :
            cubeUpperFaceCoord Q i < x i ∧
              x i < cubeUpperFaceCoord Q i + cubeScaleFactor Q := by
          simpa [cubeFaceReflectionCellCoordSet, h0, h1] using hcoord
        constructor
        · have hLowerCell :
              cubeLowerFaceCoord (cubeFaceReflectionCellCube Q choice) i < x i := by
            simpa [cubeLowerFaceCoord_cubeFaceReflectionCellCube_of_choice_upper
              Q choice h0 h1] using hstrip.1
          simpa [cubeLowerFaceCoord] using hLowerCell
        · have hUpperCell :
              x i < cubeUpperFaceCoord (cubeFaceReflectionCellCube Q choice) i := by
            simpa [cubeUpperFaceCoord_cubeFaceReflectionCellCube_of_choice_upper
              Q choice h0 h1] using hstrip.2
          simpa [cubeUpperFaceCoord] using hUpperCell

/-- Coordinatewise fold from the all-coordinate reflection block back toward
the original cube. Below the lower face it reflects through the lower face,
inside the cube it is the identity, and above the upper face it reflects
through the upper face. -/
def cubeCoordinateFold {d : ℕ} (Q : TriadicCube d) (x : Vec d) : Vec d :=
  fun i =>
    if x i < cubeLowerFaceCoord Q i then
      2 * cubeLowerFaceCoord Q i - x i
    else if x i < cubeUpperFaceCoord Q i then
      x i
    else
      2 * cubeUpperFaceCoord Q i - x i

/-- Sign contributed to a vector component by the coordinatewise fold. The
component changes sign exactly when that coordinate was reflected through one
of the two faces. -/
def cubeCoordinateFoldSign {d : ℕ} (Q : TriadicCube d) (x : Vec d)
    (i : Fin d) : ℝ :=
  if x i < cubeLowerFaceCoord Q i then
    -1
  else if x i < cubeUpperFaceCoord Q i then
    1
  else
    -1

/-- Scalar field pulled back by the all-coordinate fold. -/
def cubeCoordinateFoldReflectedScalar {d : ℕ}
    (Q : TriadicCube d) (F : Vec d → ℝ) : Vec d → ℝ :=
  fun x => F (cubeCoordinateFold Q x)

/-- Vector field pulled back by the all-coordinate fold with the reflection
sign in each component. -/
def cubeCoordinateFoldReflectedVectorField {d : ℕ}
    (Q : TriadicCube d) (G : Vec d → Vec d) : Vec d → Vec d :=
  fun x i => cubeCoordinateFoldSign Q x i * G (cubeCoordinateFold Q x) i

/-- The affine fold map associated to one reflection-block cell.  It is the
same as `cubeCoordinateFold` on that cell, but has no `x`-dependent
branching. -/
def cubeFaceReflectionCellFoldMap {d : ℕ}
    (Q : TriadicCube d) (choice : Fin d → Fin 3) : Vec d → Vec d :=
  fun x i =>
    if choice i = 0 then
      2 * cubeLowerFaceCoord Q i - x i
    else if choice i = 1 then
      x i
    else
      2 * cubeUpperFaceCoord Q i - x i

/-- Linear part of the affine fold map associated to a reflection-block cell:
original-coordinate choices have sign `+1`, reflected choices have sign `-1`.
-/
def cubeFaceReflectionCellFoldLinear {d : ℕ}
    (choice : Fin d → Fin 3) : Vec d →L[ℝ] Vec d :=
  ContinuousLinearMap.pi fun i : Fin d =>
    if choice i = 1 then
      ContinuousLinearMap.proj i
    else
      -ContinuousLinearMap.proj i

@[simp] theorem cubeFaceReflectionCellFoldLinear_apply {d : ℕ}
    (choice : Fin d → Fin 3) (v : Vec d) (i : Fin d) :
    cubeFaceReflectionCellFoldLinear choice v i =
      if choice i = 1 then v i else -v i := by
  by_cases h1 : choice i = 1 <;>
    simp [cubeFaceReflectionCellFoldLinear, h1]

theorem cubeFaceReflectionCellFoldLinear_basisVec {d : ℕ}
    (choice : Fin d → Fin 3) (k : Fin d) :
    cubeFaceReflectionCellFoldLinear choice (basisVec k) =
      (if choice k = 1 then (1 : ℝ) else -1) • basisVec k := by
  ext j
  by_cases hkj : k = j
  · subst k
    by_cases h1 : choice j = 1 <;> simp [h1]
  · have hjk : j ≠ k := fun h => hkj h.symm
    by_cases h1j : choice j = 1 <;>
      by_cases h1k : choice k = 1 <;>
        simp [hjk, h1j, h1k]

theorem cubeFaceReflectionCellFoldLinear_involutive {d : ℕ}
    (choice : Fin d → Fin 3) :
    Function.Involutive (cubeFaceReflectionCellFoldLinear choice) := by
  intro v
  ext i
  by_cases h1 : choice i = 1 <;> simp [h1]

theorem vecDot_cubeFaceReflectionCellFoldLinear_left {d : ℕ}
    (choice : Fin d → Fin 3) (v w : Vec d) :
    vecDot (cubeFaceReflectionCellFoldLinear choice v) w =
      vecDot v (cubeFaceReflectionCellFoldLinear choice w) := by
  classical
  simp [vecDot, mul_comm]

theorem cubeFaceReflectionCellFoldMap_involutive {d : ℕ}
    (Q : TriadicCube d) (choice : Fin d → Fin 3) :
    Function.Involutive (cubeFaceReflectionCellFoldMap Q choice) := by
  intro x
  ext i
  by_cases h0 : choice i = 0
  · simp [cubeFaceReflectionCellFoldMap, h0]
  · by_cases h1 : choice i = 1
    · simp [cubeFaceReflectionCellFoldMap, h1]
    · simp [cubeFaceReflectionCellFoldMap, h0, h1]

theorem injective_cubeFaceReflectionCellFoldMap {d : ℕ}
    (Q : TriadicCube d) (choice : Fin d → Fin 3) :
    Function.Injective (cubeFaceReflectionCellFoldMap Q choice) := by
  intro x y hxy
  have h := congrArg (cubeFaceReflectionCellFoldMap Q choice) hxy
  simpa [cubeFaceReflectionCellFoldMap_involutive Q choice x,
    cubeFaceReflectionCellFoldMap_involutive Q choice y] using h

theorem continuous_cubeFaceReflectionCellFoldMap {d : ℕ}
    (Q : TriadicCube d) (choice : Fin d → Fin 3) :
    Continuous (cubeFaceReflectionCellFoldMap Q choice) := by
  rw [continuous_pi_iff]
  intro i
  by_cases h0 : choice i = 0
  · simp [cubeFaceReflectionCellFoldMap, h0]
    continuity
  · by_cases h1 : choice i = 1
    · simpa [cubeFaceReflectionCellFoldMap, h1] using continuous_apply i
    · simp [cubeFaceReflectionCellFoldMap, h0, h1]
      continuity

/-- The affine fold map associated to a reflection cell, as a homeomorphism.
Its inverse is itself. -/
def cubeFaceReflectionCellFoldHomeomorph {d : ℕ}
    (Q : TriadicCube d) (choice : Fin d → Fin 3) : Vec d ≃ₜ Vec d where
  toEquiv :=
    { toFun := cubeFaceReflectionCellFoldMap Q choice
      invFun := cubeFaceReflectionCellFoldMap Q choice
      left_inv := cubeFaceReflectionCellFoldMap_involutive Q choice
      right_inv := cubeFaceReflectionCellFoldMap_involutive Q choice }
  continuous_toFun := continuous_cubeFaceReflectionCellFoldMap Q choice
  continuous_invFun := continuous_cubeFaceReflectionCellFoldMap Q choice

/-- The affine fold map associated to a reflection cell is smooth. -/
theorem contDiff_cubeFaceReflectionCellFoldMap {d : ℕ}
    (Q : TriadicCube d) (choice : Fin d → Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (cubeFaceReflectionCellFoldMap Q choice) := by
  rw [contDiff_pi]
  intro i
  by_cases h0 : choice i = 0
  · simpa [cubeFaceReflectionCellFoldMap, h0] using
      (contDiff_const.sub (contDiff_apply ℝ ℝ i) :
        ContDiff ℝ (⊤ : ℕ∞) fun x : Vec d => (2 * cubeLowerFaceCoord Q i) - x i)
  · by_cases h1 : choice i = 1
    · simpa [cubeFaceReflectionCellFoldMap, h0, h1] using
        (contDiff_apply ℝ ℝ i : ContDiff ℝ (⊤ : ℕ∞) fun x : Vec d => x i)
    · simpa [cubeFaceReflectionCellFoldMap, h0, h1] using
        (contDiff_const.sub (contDiff_apply ℝ ℝ i) :
          ContDiff ℝ (⊤ : ℕ∞) fun x : Vec d => (2 * cubeUpperFaceCoord Q i) - x i)

/-- Smoothness of a compact-test function is preserved by precomposition with
the affine fold map of a reflection cell. -/
theorem contDiff_comp_cubeFaceReflectionCellFoldMap {d : ℕ}
    (Q : TriadicCube d) (choice : Fin d → Fin 3)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x => φ (cubeFaceReflectionCellFoldMap Q choice x)) := by
  simpa [Function.comp_def] using
    hφ.comp (contDiff_cubeFaceReflectionCellFoldMap Q choice)

/-- The Fréchet derivative of a reflection-cell fold map is its diagonal
linear reflection part. -/
theorem fderiv_cubeFaceReflectionCellFoldMap {d : ℕ}
    (Q : TriadicCube d) (choice : Fin d → Fin 3) (x : Vec d) :
    fderiv ℝ (cubeFaceReflectionCellFoldMap Q choice) x =
      cubeFaceReflectionCellFoldLinear choice := by
  rw [fderiv_pi]
  · ext v i
    by_cases h0 : choice i = 0
    · have hderiv :
          fderiv ℝ (fun y : Vec d => (2 * cubeLowerFaceCoord Q i) - y i) x =
            -ContinuousLinearMap.proj i := by
          rw [fderiv_const_sub]
          exact
            congrArg Neg.neg
              (hasFDerivAt_apply (𝕜 := ℝ) i x).fderiv
      simp [cubeFaceReflectionCellFoldMap, h0, hderiv]
    · by_cases h1 : choice i = 1
      · have hderiv :
            fderiv ℝ (fun y : Vec d => y i) x =
              ContinuousLinearMap.proj i := by
          exact (hasFDerivAt_apply (𝕜 := ℝ) i x).fderiv
        simp [cubeFaceReflectionCellFoldMap, h1, hderiv]
      · have hderiv :
            fderiv ℝ (fun y : Vec d => (2 * cubeUpperFaceCoord Q i) - y i) x =
              -ContinuousLinearMap.proj i := by
          rw [fderiv_const_sub]
          exact
            congrArg Neg.neg
              (hasFDerivAt_apply (𝕜 := ℝ) i x).fderiv
        simp [cubeFaceReflectionCellFoldMap, h0, h1, hderiv]
  · intro i
    by_cases h0 : choice i = 0
    · simpa [cubeFaceReflectionCellFoldMap, h0] using
        (((hasFDerivAt_apply (𝕜 := ℝ) i x).const_sub
            (2 * cubeLowerFaceCoord Q i)).differentiableAt)
    · by_cases h1 : choice i = 1
      · simpa [cubeFaceReflectionCellFoldMap, h0, h1] using
          ((hasFDerivAt_apply (𝕜 := ℝ) i x).differentiableAt)
      · simpa [cubeFaceReflectionCellFoldMap, h0, h1] using
          (((hasFDerivAt_apply (𝕜 := ℝ) i x).const_sub
              (2 * cubeUpperFaceCoord Q i)).differentiableAt)

/-- Chain rule for gradients after precomposing a smooth test with a
reflection-cell fold map. -/
theorem euclideanGradient_comp_cubeFaceReflectionCellFoldMap {d : ℕ}
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (Q : TriadicCube d) (choice : Fin d → Fin 3) (x : Vec d) :
    euclideanGradient
        (fun y => φ (cubeFaceReflectionCellFoldMap Q choice y)) x =
      cubeFaceReflectionCellFoldLinear choice
        (euclideanGradient φ (cubeFaceReflectionCellFoldMap Q choice x)) := by
  have hcomp :
      fderiv ℝ
          (fun y => φ (cubeFaceReflectionCellFoldMap Q choice y)) x =
        (fderiv ℝ φ (cubeFaceReflectionCellFoldMap Q choice x)).comp
          (cubeFaceReflectionCellFoldLinear choice) := by
    change
      fderiv ℝ (φ ∘ cubeFaceReflectionCellFoldMap Q choice) x =
        (fderiv ℝ φ (cubeFaceReflectionCellFoldMap Q choice x)).comp
          (cubeFaceReflectionCellFoldLinear choice)
    rw [fderiv_comp]
    · rw [fderiv_cubeFaceReflectionCellFoldMap]
    · exact
        (hφ.differentiable (by simp))
          (cubeFaceReflectionCellFoldMap Q choice x)
    · exact
        (contDiff_cubeFaceReflectionCellFoldMap Q choice).differentiable
          (by simp) x
  ext k
  unfold euclideanGradient euclideanCoordDeriv
  rw [hcomp]
  rw [ContinuousLinearMap.comp_apply]
  rw [cubeFaceReflectionCellFoldLinear_basisVec]
  by_cases h1 : choice k = 1 <;> simp [h1]

/-- Coordinate derivative chain rule for precomposition with a reflection-cell
fold map. -/
theorem euclideanCoordDeriv_comp_cubeFaceReflectionCellFoldMap {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (Q : TriadicCube d) (choice : Fin d → Fin 3) (k : Fin d)
    (x : Vec d) :
    euclideanCoordDeriv k
        (fun y => u (cubeFaceReflectionCellFoldMap Q choice y)) x =
      (if choice k = 1 then (1 : ℝ) else -1) *
        euclideanCoordDeriv k u (cubeFaceReflectionCellFoldMap Q choice x) := by
  have hgrad :=
    congrFun (euclideanGradient_comp_cubeFaceReflectionCellFoldMap
      hu Q choice x) k
  by_cases h1 : choice k = 1
  · simpa [cubeFaceReflectionCellFoldLinear, euclideanGradient,
      euclideanCoordDeriv, h1] using hgrad
  · simpa [cubeFaceReflectionCellFoldLinear, euclideanGradient,
      euclideanCoordDeriv, h1] using hgrad

/-- Second coordinate-derivative chain rule for precomposition with a
reflection-cell fold map. Each reflected coordinate contributes one sign. -/
theorem euclideanCoordSecondDeriv_comp_cubeFaceReflectionCellFoldMap {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (Q : TriadicCube d) (choice : Fin d → Fin 3)
    (k l : Fin d) (x : Vec d) :
    euclideanCoordSecondDeriv k l
        (fun y => u (cubeFaceReflectionCellFoldMap Q choice y)) x =
      ((if choice k = 1 then (1 : ℝ) else -1) *
        (if choice l = 1 then (1 : ℝ) else -1)) *
        euclideanCoordSecondDeriv k l u
          (cubeFaceReflectionCellFoldMap Q choice x) := by
  let sk : ℝ := if choice k = 1 then (1 : ℝ) else -1
  let sl : ℝ := if choice l = 1 then (1 : ℝ) else -1
  have hderiv_fun :
      euclideanCoordDeriv k
          (fun y => u (cubeFaceReflectionCellFoldMap Q choice y)) =
        fun y => sk *
          euclideanCoordDeriv k u
            (cubeFaceReflectionCellFoldMap Q choice y) := by
    funext y
    simpa [sk] using
      euclideanCoordDeriv_comp_cubeFaceReflectionCellFoldMap
        hu Q choice k y
  unfold euclideanCoordSecondDeriv
  rw [hderiv_fun]
  have hdiff :
      DifferentiableAt ℝ
        (fun y =>
          euclideanCoordDeriv k u
            (cubeFaceReflectionCellFoldMap Q choice y)) x := by
    exact (((contDiff_euclideanCoordDeriv hu k).differentiable (by simp))
      (cubeFaceReflectionCellFoldMap Q choice x)).comp x
        ((contDiff_cubeFaceReflectionCellFoldMap Q choice).differentiable
          (by simp) x)
  rw [fderiv_const_mul hdiff sk]
  change sk *
      euclideanCoordDeriv l
        (fun y =>
          euclideanCoordDeriv k u
            (cubeFaceReflectionCellFoldMap Q choice y)) x =
    (sk * sl) * euclideanCoordSecondDeriv k l u
      (cubeFaceReflectionCellFoldMap Q choice x)
  rw [euclideanCoordDeriv_comp_cubeFaceReflectionCellFoldMap
    (u := euclideanCoordDeriv k u) (contDiff_euclideanCoordDeriv hu k)
    Q choice l x]
  simp [euclideanCoordSecondDeriv, euclideanCoordDeriv, sk, sl]

/-- Diagonal second derivatives are invariant under a reflection-cell fold. -/
theorem euclideanCoordSecondDeriv_diag_comp_cubeFaceReflectionCellFoldMap {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (Q : TriadicCube d) (choice : Fin d → Fin 3)
    (k : Fin d) (x : Vec d) :
    euclideanCoordSecondDeriv k k
        (fun y => u (cubeFaceReflectionCellFoldMap Q choice y)) x =
      euclideanCoordSecondDeriv k k u
        (cubeFaceReflectionCellFoldMap Q choice x) := by
  rw [euclideanCoordSecondDeriv_comp_cubeFaceReflectionCellFoldMap
    hu Q choice k k x]
  by_cases hk : choice k = 1 <;> simp [hk]

/-- The coordinate Laplacian is invariant under a reflection-cell fold. -/
theorem euclideanCoordLaplacian_comp_cubeFaceReflectionCellFoldMap {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (Q : TriadicCube d) (choice : Fin d → Fin 3) (x : Vec d) :
    euclideanCoordLaplacian
        (fun y => u (cubeFaceReflectionCellFoldMap Q choice y)) x =
      euclideanCoordLaplacian u
        (cubeFaceReflectionCellFoldMap Q choice x) := by
  unfold euclideanCoordLaplacian
  apply Finset.sum_congr rfl
  intro k _hk
  exact euclideanCoordSecondDeriv_diag_comp_cubeFaceReflectionCellFoldMap
    hu Q choice k x

/-- The pointwise squared Hessian sum is invariant under a reflection-cell
fold. -/
theorem sum_sq_euclideanCoordSecondDeriv_comp_cubeFaceReflectionCellFoldMap
    {d : ℕ} {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (Q : TriadicCube d) (choice : Fin d → Fin 3) (x : Vec d) :
    (∑ k : Fin d, ∑ l : Fin d,
        (euclideanCoordSecondDeriv k l
          (fun y => u (cubeFaceReflectionCellFoldMap Q choice y)) x) ^ 2) =
      ∑ k : Fin d, ∑ l : Fin d,
        (euclideanCoordSecondDeriv k l u
          (cubeFaceReflectionCellFoldMap Q choice x)) ^ 2 := by
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro l _hl
  rw [euclideanCoordSecondDeriv_comp_cubeFaceReflectionCellFoldMap
    hu Q choice k l x]
  by_cases hk : choice k = 1 <;> by_cases hl : choice l = 1 <;>
    simp [hk, hl, pow_two]

/-- Compact support of a test function is preserved by precomposition with
the affine fold map of a reflection cell. -/
theorem hasCompactSupport_comp_cubeFaceReflectionCellFoldMap {d : ℕ}
    (Q : TriadicCube d) (choice : Fin d → Fin 3)
    {φ : Vec d → ℝ} (hφ : HasCompactSupport φ) :
    HasCompactSupport
      (fun x => φ (cubeFaceReflectionCellFoldMap Q choice x)) := by
  show HasCompactSupport (φ ∘ cubeFaceReflectionCellFoldHomeomorph Q choice)
  simpa [Function.comp, cubeFaceReflectionCellFoldHomeomorph] using
    hφ.comp_homeomorph (cubeFaceReflectionCellFoldHomeomorph Q choice)

theorem measurableEmbedding_cubeFaceReflectionCellFoldMap {d : ℕ}
    (Q : TriadicCube d) (choice : Fin d → Fin 3) :
    MeasurableEmbedding (cubeFaceReflectionCellFoldMap Q choice) :=
  (continuous_cubeFaceReflectionCellFoldMap Q choice).measurableEmbedding
    (injective_cubeFaceReflectionCellFoldMap Q choice)

theorem measurePreserving_cubeFaceReflectionCellFoldMap {d : ℕ}
    (Q : TriadicCube d) (choice : Fin d → Fin 3) :
    MeasurePreserving (cubeFaceReflectionCellFoldMap Q choice) := by
  let f : (i : Fin d) → ℝ → ℝ :=
    fun i =>
      if choice i = 0 then
        realFaceReflection (cubeLowerFaceCoord Q i)
      else if choice i = 1 then
        id
      else
        realFaceReflection (cubeUpperFaceCoord Q i)
  have hf : ∀ i : Fin d, MeasurePreserving (f i) := by
    intro i
    by_cases h0 : choice i = 0
    · simp [f, h0, measurePreserving_realFaceReflection]
    · by_cases h1 : choice i = 1
      · simp [f, h1, MeasurePreserving.id (volume : Measure ℝ)]
      · simp [f, h0, h1, measurePreserving_realFaceReflection]
  have hpi :
      MeasurePreserving (fun x : Vec d => fun i : Fin d => f i (x i)) :=
    volume_preserving_pi hf
  convert hpi using 1
  ext x i
  by_cases h0 : choice i = 0
  · simp [cubeFaceReflectionCellFoldMap, f, h0, realFaceReflection]
  · by_cases h1 : choice i = 1
    · simp [cubeFaceReflectionCellFoldMap, f, h1]
    · simp [cubeFaceReflectionCellFoldMap, f, h0, h1, realFaceReflection]

/-- The cell fold map carries exactly its associated reflection-block cell
onto the original open cube. -/
theorem preimage_cubeFaceReflectionCellFoldMap_openCubeSet {d : ℕ}
    (Q : TriadicCube d) (choice : Fin d → Fin 3) :
    cubeFaceReflectionCellFoldMap Q choice ⁻¹' openCubeSet Q =
      openCubeSet (cubeFaceReflectionCellCube Q choice) := by
  suffices
      cubeFaceReflectionCellFoldMap Q choice ⁻¹' openCubeSet Q =
        cubeFaceReflectionCellSet Q choice by
    simpa [openCubeSet_cubeFaceReflectionCellCube] using this
  ext x
  constructor
  · intro hx i
    let l := cubeLowerFaceCoord Q i
    let u := cubeUpperFaceCoord Q i
    let s := cubeScaleFactor Q
    have hu : u = l + s := by
      dsimp [u, l, s, cubeUpperFaceCoord, cubeLowerFaceCoord,
        cubeScaleFactor]
      ring
    have hxQ :
        l < cubeFaceReflectionCellFoldMap Q choice x i ∧
          cubeFaceReflectionCellFoldMap Q choice x i < u := by
      simpa [l, u, cubeLowerFaceCoord, cubeUpperFaceCoord] using hx i
    by_cases h0 : choice i = 0
    · have hq : l < 2 * l - x i ∧ 2 * l - x i < u := by
        simpa [cubeFaceReflectionCellFoldMap, h0, l] using hxQ
      have hLower : l - s < x i := by
        rw [hu] at hq
        linarith
      have hUpper : x i < l := by
        linarith
      simpa [cubeFaceReflectionCellCoordSet, h0, l, s] using
        And.intro hLower hUpper
    · by_cases h1 : choice i = 1
      · have hq : l < x i ∧ x i < u := by
          simpa [cubeFaceReflectionCellFoldMap, h0, h1, l, u] using hxQ
        simpa [cubeFaceReflectionCellCoordSet, h0, h1, l, u] using hq
      · have hq : l < 2 * u - x i ∧ 2 * u - x i < u := by
          simpa [cubeFaceReflectionCellFoldMap, h0, h1, u] using hxQ
        have hLower : u < x i := by
          linarith
        have hUpper : x i < u + s := by
          rw [hu] at hq
          linarith
        simpa [cubeFaceReflectionCellCoordSet, h0, h1, u, s] using
          And.intro hLower hUpper
  · intro hx i
    let l := cubeLowerFaceCoord Q i
    let u := cubeUpperFaceCoord Q i
    let s := cubeScaleFactor Q
    have hu : u = l + s := by
      dsimp [u, l, s, cubeUpperFaceCoord, cubeLowerFaceCoord,
        cubeScaleFactor]
      ring
    have hcoord := hx i
    have hfold :
        cubeLowerFaceCoord Q i <
            cubeFaceReflectionCellFoldMap Q choice x i ∧
          cubeFaceReflectionCellFoldMap Q choice x i <
            cubeUpperFaceCoord Q i := by
      by_cases h0 : choice i = 0
      · have hstrip : l - s < x i ∧ x i < l := by
          simpa [cubeFaceReflectionCellCoordSet, h0, l, s] using hcoord
        constructor
        · simpa [cubeFaceReflectionCellFoldMap, h0, l,
            cubeLowerFaceCoord] using (by linarith : l < 2 * l - x i)
        · have hlt : 2 * l - x i < u := by
            rw [hu]
            linarith
          simpa [cubeFaceReflectionCellFoldMap, h0, l, u,
            cubeUpperFaceCoord] using hlt
      · by_cases h1 : choice i = 1
        · have hstrip : l < x i ∧ x i < u := by
            simpa [cubeFaceReflectionCellCoordSet, h0, h1, l, u] using
              hcoord
          simpa [cubeFaceReflectionCellFoldMap, h0, h1, l, u,
            cubeLowerFaceCoord, cubeUpperFaceCoord] using hstrip
        · have hstrip : u < x i ∧ x i < u + s := by
            simpa [cubeFaceReflectionCellCoordSet, h0, h1, u, s] using
              hcoord
          constructor
          · have hlt : l < 2 * u - x i := by
              rw [hu]
              linarith
            simpa [cubeFaceReflectionCellFoldMap, h0, h1, u, l,
              cubeLowerFaceCoord] using hlt
          · simpa [cubeFaceReflectionCellFoldMap, h0, h1, u,
              cubeUpperFaceCoord] using (by linarith : 2 * u - x i < u)
    simpa [cubeLowerFaceCoord, cubeUpperFaceCoord] using hfold

/-- Change variables from a reflection-block cell to the original open cube
using the cell fold map. -/
theorem setIntegral_cubeFaceReflectionCellCube_comp_cellFoldMap {d : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : TriadicCube d) (choice : Fin d → Fin 3) (g : Vec d → E) :
    ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        g (cubeFaceReflectionCellFoldMap Q choice x) ∂volume =
      ∫ y in openCubeSet Q, g y ∂volume := by
  rw [← preimage_cubeFaceReflectionCellFoldMap_openCubeSet Q choice]
  exact (measurePreserving_cubeFaceReflectionCellFoldMap Q choice).setIntegral_preimage_emb
    (measurableEmbedding_cubeFaceReflectionCellFoldMap Q choice) g
    (openCubeSet Q)

/-- Integrability transports from the original open cube to a reflection-block
cell by precomposition with the cell fold map. -/
theorem integrable_cubeFaceReflectionCellCube_comp_cellFoldMap {d : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q : TriadicCube d} {choice : Fin d → Fin 3} {g : Vec d → E}
    (hg :
      MeasureTheory.Integrable g (volume.restrict (openCubeSet Q))) :
    MeasureTheory.Integrable
      (fun x => g (cubeFaceReflectionCellFoldMap Q choice x))
      (volume.restrict (openCubeSet (cubeFaceReflectionCellCube Q choice))) := by
  have hmp :=
    (measurePreserving_cubeFaceReflectionCellFoldMap Q choice).restrict_preimage_emb
      (measurableEmbedding_cubeFaceReflectionCellFoldMap Q choice)
      (openCubeSet Q)
  simpa [preimage_cubeFaceReflectionCellFoldMap_openCubeSet Q choice,
    Function.comp_def] using hmp.integrable_comp_of_integrable hg

end

end Homogenization
