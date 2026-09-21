/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMeasure
import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicCubeTranslation
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.EuclideanL2CZ
import Mathlib.MeasureTheory.Group.Measure

/-! # Reflections -/

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal Topology

/-!
# Cube face reflections

This file begins the C.2 reflection infrastructure for the cube Neumann
`W^{2,2}` discharge.  The key analytic reflection step will be proved in weak
form; the lemmas here supply the affine one-coordinate face reflections and
their first coordinate-derivative chain rule.
-/

noncomputable section

/-- One-dimensional reflection through the point `a`. -/
def realFaceReflection (a : ℝ) : ℝ → ℝ :=
  fun t => 2 * a - t

/-- Lower coordinate face of a triadic cube. -/
def cubeLowerFaceCoord {d : ℕ} (Q : TriadicCube d) (i : Fin d) : ℝ :=
  (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q)

/-- Upper coordinate face of a triadic cube. -/
def cubeUpperFaceCoord {d : ℕ} (Q : TriadicCube d) (i : Fin d) : ℝ :=
  (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q)

/-- Linear part of reflection in the coordinate hyperplane normal to `basisVec i`. -/
def coordReflectionLinear {d : ℕ} (i : Fin d) : Vec d →L[ℝ] Vec d :=
  ContinuousLinearMap.pi fun j : Fin d =>
    if j = i then -ContinuousLinearMap.proj j else ContinuousLinearMap.proj j

/-- Translation offset for the affine reflection through the face coordinate `a`. -/
def coordFaceReflectionOffset {d : ℕ} (a : ℝ) (i : Fin d) : Vec d :=
  fun j => if j = i then 2 * a else 0

/-- Reflection through the coordinate hyperplane `{x_i = a}`. -/
def coordFaceReflection {d : ℕ} (a : ℝ) (i : Fin d) : Vec d → Vec d :=
  fun x => coordReflectionLinear i x + coordFaceReflectionOffset a i

/-- Reflection through the upper `i`-face of `Q`. -/
def cubeUpperFaceReflection {d : ℕ} (Q : TriadicCube d) (i : Fin d) :
    Vec d → Vec d :=
  coordFaceReflection (cubeUpperFaceCoord Q i) i

/-- Reflection through the lower `i`-face of `Q`. -/
def cubeLowerFaceReflection {d : ℕ} (Q : TriadicCube d) (i : Fin d) :
    Vec d → Vec d :=
  coordFaceReflection (cubeLowerFaceCoord Q i) i

/-- Integer coordinate shift by `n` in one coordinate and zero tangentially. -/
def coordIndexShift {d : ℕ} (i : Fin d) (n : ℤ) : Fin d → ℤ :=
  fun j => if j = i then n else 0

/-- Same-scale cube adjacent to `Q` across its upper `i`-face. -/
def cubeUpperFaceNeighbor {d : ℕ} (Q : TriadicCube d) (i : Fin d) :
    TriadicCube d :=
  translateCube (coordIndexShift i 1) Q

/-- Same-scale cube adjacent to `Q` across its lower `i`-face. -/
def cubeLowerFaceNeighbor {d : ℕ} (Q : TriadicCube d) (i : Fin d) :
    TriadicCube d :=
  translateCube (coordIndexShift i (-1)) Q

@[simp] theorem cubeLowerFaceCoord_cubeLowerFaceNeighbor_self {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) :
    cubeLowerFaceCoord (cubeLowerFaceNeighbor Q i) i =
      cubeLowerFaceCoord Q i - cubeScaleFactor Q := by
  simp [cubeLowerFaceCoord, cubeLowerFaceNeighbor, coordIndexShift,
    translateCube, cubeScaleFactor]
  ring_nf

@[simp] theorem cubeUpperFaceCoord_cubeLowerFaceNeighbor_self {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) :
    cubeUpperFaceCoord (cubeLowerFaceNeighbor Q i) i =
      cubeLowerFaceCoord Q i := by
  simp [cubeUpperFaceCoord, cubeLowerFaceCoord, cubeLowerFaceNeighbor,
    coordIndexShift, translateCube, cubeScaleFactor]
  ring_nf
  left
  trivial

@[simp] theorem cubeLowerFaceCoord_cubeUpperFaceNeighbor_self {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) :
    cubeLowerFaceCoord (cubeUpperFaceNeighbor Q i) i =
      cubeUpperFaceCoord Q i := by
  simp [cubeLowerFaceCoord, cubeUpperFaceCoord, cubeUpperFaceNeighbor,
    coordIndexShift, translateCube, cubeScaleFactor]
  ring_nf
  left
  trivial

@[simp] theorem cubeUpperFaceCoord_cubeUpperFaceNeighbor_self {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) :
    cubeUpperFaceCoord (cubeUpperFaceNeighbor Q i) i =
      cubeUpperFaceCoord Q i + cubeScaleFactor Q := by
  simp [cubeUpperFaceCoord, cubeUpperFaceNeighbor, coordIndexShift,
    translateCube, cubeScaleFactor]
  ring_nf

@[simp] theorem cubeLowerFaceCoord_cubeLowerFaceNeighbor_ne {d : ℕ}
    (Q : TriadicCube d) {i j : Fin d} (hji : j ≠ i) :
    cubeLowerFaceCoord (cubeLowerFaceNeighbor Q i) j =
      cubeLowerFaceCoord Q j := by
  simp [cubeLowerFaceCoord, cubeLowerFaceNeighbor, coordIndexShift,
    translateCube, cubeScaleFactor, hji]

@[simp] theorem cubeUpperFaceCoord_cubeLowerFaceNeighbor_ne {d : ℕ}
    (Q : TriadicCube d) {i j : Fin d} (hji : j ≠ i) :
    cubeUpperFaceCoord (cubeLowerFaceNeighbor Q i) j =
      cubeUpperFaceCoord Q j := by
  simp [cubeUpperFaceCoord, cubeLowerFaceNeighbor, coordIndexShift,
    translateCube, cubeScaleFactor, hji]

@[simp] theorem cubeLowerFaceCoord_cubeUpperFaceNeighbor_ne {d : ℕ}
    (Q : TriadicCube d) {i j : Fin d} (hji : j ≠ i) :
    cubeLowerFaceCoord (cubeUpperFaceNeighbor Q i) j =
      cubeLowerFaceCoord Q j := by
  simp [cubeLowerFaceCoord, cubeUpperFaceNeighbor, coordIndexShift,
    translateCube, cubeScaleFactor, hji]

@[simp] theorem cubeUpperFaceCoord_cubeUpperFaceNeighbor_ne {d : ℕ}
    (Q : TriadicCube d) {i j : Fin d} (hji : j ≠ i) :
    cubeUpperFaceCoord (cubeUpperFaceNeighbor Q i) j =
      cubeUpperFaceCoord Q j := by
  simp [cubeUpperFaceCoord, cubeUpperFaceNeighbor, coordIndexShift,
    translateCube, cubeScaleFactor, hji]

@[simp] theorem coordReflectionLinear_apply {d : ℕ}
    (i : Fin d) (x : Vec d) (j : Fin d) :
    coordReflectionLinear i x j = if j = i then -x j else x j := by
  by_cases h : j = i <;> simp [coordReflectionLinear, h]

theorem vecDot_coordReflectionLinear_left {d : ℕ}
    (i : Fin d) (v w : Vec d) :
    vecDot (coordReflectionLinear i v) w =
      vecDot v (coordReflectionLinear i w) := by
  unfold vecDot
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hji : j = i <;> simp [hji]

theorem vecDot_coordReflectionLinear_coordReflectionLinear {d : ℕ}
    (i : Fin d) (v w : Vec d) :
    vecDot (coordReflectionLinear i v) (coordReflectionLinear i w) =
      vecDot v w := by
  rw [vecDot_coordReflectionLinear_left]
  unfold vecDot
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hji : j = i <;> simp [hji]

@[simp] theorem coordFaceReflection_apply {d : ℕ}
    (a : ℝ) (i : Fin d) (x : Vec d) (j : Fin d) :
    coordFaceReflection a i x j = if j = i then 2 * a - x j else x j := by
  by_cases h : j = i
  · subst h
    simp [coordFaceReflection, coordFaceReflectionOffset]
    ring
  · simp [coordFaceReflection, coordFaceReflectionOffset, h]

@[simp] theorem coordFaceReflection_apply_self {d : ℕ}
    (a : ℝ) (i : Fin d) (x : Vec d) :
    coordFaceReflection a i x i = 2 * a - x i := by
  simp

theorem coordFaceReflection_apply_ne {d : ℕ}
    (a : ℝ) (i j : Fin d) (x : Vec d) (hji : j ≠ i) :
    coordFaceReflection a i x j = x j := by
  simp [hji]

@[simp] theorem realFaceReflection_apply (a t : ℝ) :
    realFaceReflection a t = 2 * a - t := rfl

theorem continuous_coordFaceReflection {d : ℕ}
    (a : ℝ) (i : Fin d) :
    Continuous (coordFaceReflection (d := d) a i) := by
  unfold coordFaceReflection
  exact (coordReflectionLinear i).continuous.add continuous_const

theorem continuous_cubeUpperFaceReflection {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) :
    Continuous (cubeUpperFaceReflection Q i) := by
  simpa [cubeUpperFaceReflection] using
    continuous_coordFaceReflection (d := d) (cubeUpperFaceCoord Q i) i

theorem continuous_cubeLowerFaceReflection {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) :
    Continuous (cubeLowerFaceReflection Q i) := by
  simpa [cubeLowerFaceReflection] using
    continuous_coordFaceReflection (d := d) (cubeLowerFaceCoord Q i) i

theorem contDiff_coordFaceReflection {d : ℕ}
    (a : ℝ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (coordFaceReflection (d := d) a i) := by
  unfold coordFaceReflection
  exact (coordReflectionLinear i).contDiff.add contDiff_const

theorem contDiff_cubeUpperFaceReflection {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (cubeUpperFaceReflection Q i) := by
  simpa [cubeUpperFaceReflection] using
    contDiff_coordFaceReflection (d := d) (cubeUpperFaceCoord Q i) i

theorem contDiff_cubeLowerFaceReflection {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (cubeLowerFaceReflection Q i) := by
  simpa [cubeLowerFaceReflection] using
    contDiff_coordFaceReflection (d := d) (cubeLowerFaceCoord Q i) i

theorem measurePreserving_realFaceReflection (a : ℝ) :
    MeasurePreserving (realFaceReflection a) := by
  have hneg : MeasurePreserving (fun t : ℝ => -t) :=
    Measure.measurePreserving_neg (volume : Measure ℝ)
  have htranslate : MeasurePreserving (fun t : ℝ => t + 2 * a) :=
    measurePreserving_add_right (volume : Measure ℝ) (2 * a)
  convert htranslate.comp hneg using 1
  ext t
  simp [realFaceReflection, sub_eq_add_neg, add_comm]

theorem measurePreserving_coordFaceReflection {d : ℕ}
    (a : ℝ) (i : Fin d) :
    MeasurePreserving (coordFaceReflection (d := d) a i) := by
  let f : (j : Fin d) → ℝ → ℝ :=
    fun j => if j = i then realFaceReflection a else id
  have hf : ∀ j : Fin d, MeasurePreserving (f j) := by
    intro j
    by_cases hji : j = i
    · simp [f, hji, measurePreserving_realFaceReflection a]
    · simp [f, hji, MeasurePreserving.id (volume : Measure ℝ)]
  have hpi :
      MeasurePreserving (fun x : Vec d => fun j : Fin d => f j (x j)) :=
    volume_preserving_pi hf
  convert hpi using 1
  ext x j
  by_cases hji : j = i <;> simp [f, hji, realFaceReflection]

theorem measurePreserving_cubeUpperFaceReflection {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) :
    MeasurePreserving (cubeUpperFaceReflection Q i) := by
  simpa [cubeUpperFaceReflection] using
    measurePreserving_coordFaceReflection (d := d) (cubeUpperFaceCoord Q i) i

theorem measurePreserving_cubeLowerFaceReflection {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) :
    MeasurePreserving (cubeLowerFaceReflection Q i) := by
  simpa [cubeLowerFaceReflection] using
    measurePreserving_coordFaceReflection (d := d) (cubeLowerFaceCoord Q i) i

theorem cubeUpperFaceReflection_mem_openCubeSet_of_mem_neighbor {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) {x : Vec d}
    (hx : x ∈ openCubeSet (cubeUpperFaceNeighbor Q i)) :
    cubeUpperFaceReflection Q i x ∈ openCubeSet Q := by
  intro j
  by_cases hji : j = i
  · subst j
    have hscale : 0 < cubeScaleFactor Q := by
      simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
    have hxi := hx i
    simp [cubeUpperFaceNeighbor, coordIndexShift, cubeUpperFaceReflection,
      cubeUpperFaceCoord, translateCube, cubeScaleFactor] at hxi ⊢
    constructor <;> nlinarith [hscale]
  · have hxj := hx j
    simpa [openCubeSet, cubeUpperFaceNeighbor, coordIndexShift, cubeUpperFaceReflection,
      cubeUpperFaceCoord, translateCube, hji] using! hxj

theorem cubeUpperFaceReflection_mem_neighbor_of_mem_openCubeSet {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) {x : Vec d}
    (hx : x ∈ openCubeSet Q) :
    cubeUpperFaceReflection Q i x ∈ openCubeSet (cubeUpperFaceNeighbor Q i) := by
  intro j
  by_cases hji : j = i
  · subst j
    have hscale : 0 < cubeScaleFactor Q := by
      simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
    have hxi := hx i
    simp [cubeUpperFaceNeighbor, coordIndexShift, cubeUpperFaceReflection,
      cubeUpperFaceCoord, translateCube, cubeScaleFactor] at hxi ⊢
    constructor <;> nlinarith [hscale]
  · have hxj := hx j
    simpa [openCubeSet, cubeUpperFaceNeighbor, coordIndexShift, cubeUpperFaceReflection,
      cubeUpperFaceCoord, translateCube, hji] using! hxj

theorem cubeLowerFaceReflection_mem_openCubeSet_of_mem_neighbor {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) {x : Vec d}
    (hx : x ∈ openCubeSet (cubeLowerFaceNeighbor Q i)) :
    cubeLowerFaceReflection Q i x ∈ openCubeSet Q := by
  intro j
  by_cases hji : j = i
  · subst j
    have hscale : 0 < cubeScaleFactor Q := by
      simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
    have hxi := hx i
    simp [cubeLowerFaceNeighbor, coordIndexShift, cubeLowerFaceReflection,
      cubeLowerFaceCoord, translateCube, cubeScaleFactor] at hxi ⊢
    constructor <;> nlinarith [hscale]
  · have hxj := hx j
    simpa [openCubeSet, cubeLowerFaceNeighbor, coordIndexShift, cubeLowerFaceReflection,
      cubeLowerFaceCoord, translateCube, hji] using! hxj

theorem cubeLowerFaceReflection_mem_neighbor_of_mem_openCubeSet {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) {x : Vec d}
    (hx : x ∈ openCubeSet Q) :
    cubeLowerFaceReflection Q i x ∈ openCubeSet (cubeLowerFaceNeighbor Q i) := by
  intro j
  by_cases hji : j = i
  · subst j
    have hscale : 0 < cubeScaleFactor Q := by
      simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
    have hxi := hx i
    simp [cubeLowerFaceNeighbor, coordIndexShift, cubeLowerFaceReflection,
      cubeLowerFaceCoord, translateCube, cubeScaleFactor] at hxi ⊢
    constructor <;> nlinarith [hscale]
  · have hxj := hx j
    simpa [openCubeSet, cubeLowerFaceNeighbor, coordIndexShift, cubeLowerFaceReflection,
      cubeLowerFaceCoord, translateCube, hji] using! hxj

/-- The open cube is disjoint from its same-scale upper face neighbor. -/
theorem disjoint_openCubeSet_cubeUpperFaceNeighbor {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) :
    Disjoint (openCubeSet Q) (openCubeSet (cubeUpperFaceNeighbor Q i)) := by
  rw [Set.disjoint_left]
  intro x hxQ hxN
  have hQupper := (hxQ i).2
  have hNlower := (hxN i).1
  have hscale : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  simp [cubeUpperFaceNeighbor, coordIndexShift, translateCube,
    cubeScaleFactor] at hQupper hNlower
  nlinarith [hscale]

/-- The open cube is disjoint from its same-scale lower face neighbor. -/
theorem disjoint_openCubeSet_cubeLowerFaceNeighbor {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) :
    Disjoint (openCubeSet Q) (openCubeSet (cubeLowerFaceNeighbor Q i)) := by
  rw [Set.disjoint_left]
  intro x hxQ hxN
  have hQlower := (hxQ i).1
  have hNupper := (hxN i).2
  have hscale : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  simp [cubeLowerFaceNeighbor, coordIndexShift, translateCube,
    cubeScaleFactor] at hQlower hNupper
  nlinarith [hscale]

/-- The lower and upper same-scale face neighbors of a cube are disjoint. -/
theorem disjoint_cubeLowerFaceNeighbor_cubeUpperFaceNeighbor {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) :
    Disjoint
      (openCubeSet (cubeLowerFaceNeighbor Q i))
      (openCubeSet (cubeUpperFaceNeighbor Q i)) := by
  rw [Set.disjoint_left]
  intro x hxL hxU
  have hLupper := (hxL i).2
  have hUlower := (hxU i).1
  have hscale : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  simp [cubeLowerFaceNeighbor, cubeUpperFaceNeighbor, coordIndexShift,
    translateCube, cubeScaleFactor] at hLupper hUlower
  norm_num at hLupper hUlower
  have hscale' : 0 < (3 : ℝ) ^ Q.scale := by
    simpa [cubeScaleFactor] using hscale
  nlinarith [hscale']


@[simp] theorem coordFaceReflection_involutive {d : ℕ}
    (a : ℝ) (i : Fin d) (x : Vec d) :
    coordFaceReflection a i (coordFaceReflection a i x) = x := by
  ext j
  by_cases hji : j = i
  · subst hji
    simp
  · simp [hji]

@[simp] theorem cubeUpperFaceReflection_involutive {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (x : Vec d) :
    cubeUpperFaceReflection Q i (cubeUpperFaceReflection Q i x) = x := by
  change coordFaceReflection (cubeUpperFaceCoord Q i) i
    (coordFaceReflection (cubeUpperFaceCoord Q i) i x) = x
  exact coordFaceReflection_involutive (cubeUpperFaceCoord Q i) i x

@[simp] theorem cubeLowerFaceReflection_involutive {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (x : Vec d) :
    cubeLowerFaceReflection Q i (cubeLowerFaceReflection Q i x) = x := by
  change coordFaceReflection (cubeLowerFaceCoord Q i) i
    (coordFaceReflection (cubeLowerFaceCoord Q i) i x) = x
  exact coordFaceReflection_involutive (cubeLowerFaceCoord Q i) i x

end

end Homogenization
