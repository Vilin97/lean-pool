/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development004
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle008
public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development002
public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development003
public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development001
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Positivity
/-!
# Moving sofa: related mathematical developments

* `Canonical.Foundations.Development001`.
* `Geometry.Foundations.Development003`.
* `Analysis.Foundations.Development003`.
* `Cap.Foundations.Development002`.
* `Analysis.Foundations.Development004`.
* `Convex.Foundations.Development002`.
* `Geometry.Foundations.Development004`.
* `Gerver.Foundations.Development002`.
* `Cap.Foundations.Development003`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Canonical.Definitions`.
* `Canonical.GerverDefinitions`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 The Formal Conjectures Authors and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors, Dean Cureton
-/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/


/-!
# Definitions for the moving sofa problem

The definitions of `MovingSofaSubmission/Challenge.lean`, copied from
`FormalConjectures/Wikipedia/MovingSofa.lean` in google-deepmind/formal-conjectures at commit
`ddfbaf90f4482030d88aae5233fe933874296a23`. Here `ABφθSpec.existsUnique` is proved, from the
certificate in GerverSofaLean, so that Gerver's constants are defined from a proved statement.
-/

public section

noncomputable section

/-- The standard two-dimensional Euclidean space over the reals. -/
scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open scoped EuclideanGeometry

/-- The plane `ℝ²` with the orientation of its standard basis, so that rotations are
counterclockwise. -/
noncomputable instance Module.orientedEuclideanSpaceFinTwo : Module.Oriented ℝ ℝ² (Fin 2) :=
  ⟨Module.Basis.orientation <| PiLp.basisFun 2 _ _⟩

/-- The plane `ℝ²` has dimension two. -/
instance fact_finrank_euclideanSpace_fin_two : Fact (Module.finrank ℝ ℝ² = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

namespace MovingSofa

open Topology
open scoped Real unitInterval EuclideanGeometry

/-- The **horizontal side** of the hallway is $(-\infty, 1] \times [0, 1]$. -/
@[expose]
def horizontalHallway : Set ℝ² := {!₂[x, y] | (x) (y) (_ : x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1)}

/-- The **vertical side** of the hallway is $[0, 1] \times (-\infty, 1]$. -/
@[expose]
def verticalHallway : Set ℝ² := {!₂[x, y] | (x) (y) (_ : 0 ≤ x ∧ x ≤ 1 ∧ y ≤ 1)}

/-- The **hallway** is the union of its horizontal and vertical sides. -/
@[expose]
def hallway : Set ℝ² := horizontalHallway ∪ verticalHallway

/-- The affine isometry group of the Euclidean plane. -/
scoped notation "E(2)" => ℝ² ≃ᵃⁱ[ℝ] ℝ²

/-- The topology on the isometry group `E(2)`, induced from the continuous affine maps of the
plane. -/
instance rigidMotionTopology : TopologicalSpace E(2) :=
  .induced (·.toAffineIsometry.toContinuousAffineMap) inferInstance

/--
A connected closed set $s$ is a **moving sofa** according to a rigid motion $m:I\to\mathrm{SE}(2)$,
if the sofa is initially in the horizontal side of the hallway and ends up in the vertical side.
Here, since $\mathrm{SE}(2)$ is not in Mathlib yet, we use $\mathrm{E}(2)$ and rely on continuity
and $m(0) = \mathrm{id}$ to ensure $m$ is in $\mathrm{SE}(2)$.
-/
structure IsMovingSofa (s : Set ℝ²) (m : I → E(2)) : Prop where
  isConnected : IsConnected s
  isClosed : IsClosed s
  continuous : Continuous m
  zero : m 0 = .refl ℝ ℝ²
  initial : s ⊆ horizontalHallway
  subset_hallway : ∀ t, m t '' s ⊆ hallway
  final : m 1 '' s ⊆ verticalHallway

/--
The rigid motion that translates by $p$ and then rotates counterclockwise by $\alpha$.
Note that [Ge92] used this definition while [Ro18] used rotation first and then translation.
-/
@[expose]
def rotateTranslate (α : Real.Angle) (p : ℝ²) : E(2) :=
  (AffineIsometryEquiv.vaddConst ℝ p).trans
    (EuclideanGeometry.o.rotation α).toAffineIsometryEquiv

/--
The sofa according to a rotation path $p : [0, \pi/2] \to \mathbb{R}^2$ as in [Ge92] is the
intersection over $\alpha \in [0, \pi/2]$ of hallways each translated by $p(\alpha)$ and then
rotated by $\alpha$, with the special cases that the hallway at $0$ is the horizontal side
and the hallway at $\pi/2$ is the vertical side.
-/
@[expose]
def sofaOfRotateTranslatePath (p : ℝ → ℝ²) : Set ℝ² :=
  rotateTranslate 0 (p 0) '' horizontalHallway ∩
  rotateTranslate ↑(π / 2) (p (π / 2)) '' verticalHallway ∩
  ⋂ α ∈ Set.Icc 0 (π / 2), rotateTranslate α (p α) '' hallway

namespace GerversSofa

/-
Gerver's constants defining the sofa.

This section follows Theorem 2 of Gerver's paper [Ge92].
-/

/--
Eq. 1-4 of [Ro18], which specifies the constants $A$, $B$, $\varphi$, and $\theta$ of [Ge92].
-/
@[expose]
def ABφθSpec (A B φ θ : ℝ) : Prop :=
  0 ≤ φ ∧ φ ≤ θ ∧ θ ≤ π / 4 ∧ 0 ≤ A ∧ 0 ≤ B ∧
  A * (θ.cos - φ.cos) - 2 * B * φ.sin
    + (θ - φ - 1) * θ.cos - θ.sin + φ.cos + φ.sin = 0 ∧
  A * (3 * θ.sin + φ.sin) - 2 * B * φ.cos
    + 3 * (θ - φ - 1) * θ.sin + 3 * θ.cos - φ.sin + φ.cos = 0 ∧
  A * φ.cos - (φ.sin + 1 / 2 - φ.cos / 2 + B * φ.sin) = 0 ∧
  (A + π / 2 - φ - θ) - (B - (θ - φ) * (1 + A) / 2 - (θ - φ)^2 / 4) = 0

/-- There exist unique constants $A$, $B$, $\varphi$, and $\theta$ satisfying the spec. -/
theorem ABφθSpec.existsUnique : ∃! ABφθ : ℝ × ℝ × ℝ × ℝ,
    ABφθSpec ABφθ.1 ABφθ.2.1 ABφθ.2.2.1 ABφθ.2.2.2 :=
  GerverSofa.PartF.Parameters.existsUnique

/-- Gerver's constant $A$: the first component of the unique solution of `ABφθSpec`. -/
@[expose]
def A : ℝ := ABφθSpec.existsUnique.choose.1
/-- Gerver's constant $B$: the second component of the unique solution of `ABφθSpec`. -/
@[expose]
def B : ℝ := ABφθSpec.existsUnique.choose.2.1
/-- Gerver's angle $\varphi$: the third component of the unique solution of `ABφθSpec`. -/
@[expose]
def φ : ℝ := ABφθSpec.existsUnique.choose.2.2.1
/-- Gerver's angle $\theta$: the fourth component of the unique solution of `ABφθSpec`. -/
@[expose]
def θ : ℝ := ABφθSpec.existsUnique.choose.2.2.2

/-- The integral-path auxiliary function $r$, with break points $\varphi$, $\theta$,
$\pi/2 - \theta$ and $\pi/2 - \varphi$. The functions `x` and `y` are integrals of it. -/
@[expose]
def r (α : ℝ) : ℝ :=
  if α ≤ φ then
    1 / 2
  else if α ≤ θ then
    (1 + A + α - φ) / 2
  else if α ≤ π / 2 - θ then
    A + α - φ
  else if α ≤ π / 2 - φ then
    B - (π / 2 - α - φ) * (1 + A) / 2 - (π / 2 - α - φ) ^ 2 / 4
  else
    0

/-- $y(\alpha) = \int_\alpha^{\pi/2 - \varphi} r(t) \sin t \, dt$, used in the canonical
integral-path definition. -/
@[expose]
def y (α : ℝ) : ℝ :=
  ∫ t in α..π / 2 - φ, r t * t.sin

/-- $x(\alpha) = 1 - \int_\alpha^{\pi/2 - \varphi} r(t) \cos t \, dt$, used in the canonical
integral-path definition. -/
@[expose]
def x (α : ℝ) : ℝ :=
  1 - ∫ t in α..π / 2 - φ, r t * t.cos

/-- The rotation path of Gerver's sofa: `p α` is the translation applied to the hallway before it
is rotated by the angle $\alpha \in [0, \pi/2]$, in the convention of `rotateTranslate`. -/
@[expose]
def p (α : ℝ) : ℝ² :=
  !₂[if α ≤ φ
      then α.cos - 1
      else x (π / 2 - α) * α.cos + y (π / 2 - α) * α.sin - 1,
    if α ≤ π / 2 - φ
      then y α * α.cos - (4 * x 0 - 2 - x α) * α.sin - 1
      else -(4 * x 0 - 3) * α.sin - 1]

end GerversSofa

/-- Gerver's sofa is the sofa according to the rotation path `GerversSofa.p`. -/
@[expose]
def gerversSofa : Set ℝ² :=
  sofaOfRotateTranslatePath GerversSofa.p

open MeasureTheory
open scoped ENNReal

/-- The **sofa constant** is the maximal area of a moving sofa. -/
@[expose]
def sofaConstant : ℝ≥0∞ := ⨆ (s : Set ℝ²) (_ : ∃ m, IsMovingSofa s m), volume s

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-
MIT License

Copyright (c) 2026 Dawid Trela

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/



/-!
# Gerver's definitions in GerverSofaLean agree with the ones used here

Adapted from `F07UpstreamAdapter` in GerverSofaLean v1.1.0 (MIT). GerverSofaLean states its results
for its own copy of the moving sofa definitions. This file identifies that copy with the
definitions of `MovingSofa.Canonical.Definitions`.
-/

public section

noncomputable section
open scoped unitInterval

namespace GerverSofa.PartF.ProjectAdapter

open Coordinates

theorem horizontalHallway_eq_model :
    MovingSofa.horizontalHallway = Model.horizontalHallway := by
  ext q
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    exact hxy
  · intro hq
    exact ⟨q 0, q 1, hq, plane_ext rfl rfl⟩

theorem verticalHallway_eq_model :
    MovingSofa.verticalHallway = Model.verticalHallway := by
  ext q
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    exact hxy
  · intro hq
    exact ⟨q 0, q 1, hq, plane_ext rfl rfl⟩

theorem hallway_eq_model : MovingSofa.hallway = Model.hallway := by
  unfold MovingSofa.hallway Model.hallway
  rw [horizontalHallway_eq_model, verticalHallway_eq_model]

theorem isMovingSofa_iff_model (s : Set Plane) (m : I → Rigid) :
    MovingSofa.IsMovingSofa s m ↔ Model.IsMovingSofa s m := by
  constructor
  · intro h
    refine ⟨h.isConnected, h.isClosed, h.continuous, h.zero, ?_, ?_, ?_⟩
    · simpa only [horizontalHallway_eq_model] using h.initial
    · intro t
      simpa only [hallway_eq_model] using h.subset_hallway t
    · simpa only [verticalHallway_eq_model] using h.final
  · intro h
    refine ⟨h.isConnected, h.isClosed, h.continuous, h.zero, ?_, ?_, ?_⟩
    · simpa only [horizontalHallway_eq_model] using h.initial
    · intro t
      simpa only [hallway_eq_model] using h.subset_hallway t
    · simpa only [verticalHallway_eq_model] using h.final

theorem sofaOfRotateTranslatePath_eq_bodySofa (p : ℝ → Plane) :
    MovingSofa.sofaOfRotateTranslatePath p =
      bodySofa p Model.horizontalHallway Model.verticalHallway Model.hallway := by
  unfold MovingSofa.sofaOfRotateTranslatePath bodySofa angleIntersection
  rw [horizontalHallway_eq_model, verticalHallway_eq_model, hallway_eq_model]
  rfl

/-- The reduced parameter tuple corresponding to the canonical choice of the unique angle
solution. -/
@[expose]
def selected : Reduced.Params :=
  PartE.tupleEquiv MovingSofa.GerversSofa.ABφθSpec.existsUnique.choose

theorem selected_eq_certified : selected = Integrals.certified := by
  have h : MovingSofa.GerversSofa.ABφθSpec.existsUnique.choose = Parameters.certified :=
    Parameters.choice_independent MovingSofa.GerversSofa.ABφθSpec.existsUnique
  exact (congrArg PartE.tupleEquiv h).trans (PartE.tupleEquiv.apply_symm_apply _)

theorem p_eq_selected (t : ℝ) :
    MovingSofa.GerversSofa.p t = toPlane (Integrals.path selected t) := rfl

theorem p_eq_certified : MovingSofa.GerversSofa.p =
    fun t => toPlane (Integrals.path Integrals.certified t) := by
  funext t
  rw [p_eq_selected, selected_eq_certified]

theorem integral_rotation_to_full (t : ℝ) (ht : t ∈ Set.Icc 0 (Real.pi / 2)) :
    rotation t (MovingSofa.GerversSofa.p t) = toPlane (Romik.path PartC.params t) := by
  rw [p_eq_certified]
  exact Integrals.certified_integral_rotation_to_full t ht

theorem gerversSofa_eq_certified : MovingSofa.gerversSofa = EuclideanMotion.sofa := by
  unfold MovingSofa.gerversSofa
  rw [sofaOfRotateTranslatePath_eq_bodySofa, p_eq_certified]
  exact Integrals.integral_sofa_eq_certified

end GerverSofa.PartF.ProjectAdapter

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Geometry.Hallway`.
* `Geometry.HallwayParts`.
* `Geometry.HallwayPartsProperties`.
* `Geometry.HallwayRay`.
* `Geometry.HallwaySupport`.
* `Geometry.Parallelogram`.
* `Geometry.ParallelogramGap`.
* `Geometry.PathHalfPlaneCap`.
* `Geometry.Reflection`.
* `Geometry.SupportingHallway`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Hallway
-/

public section

noncomputable section

namespace MovingSofa

/-- Counterclockwise rotation about the origin. -/
@[expose]
def rotationMap (t : Real.Angle) (p : Point) : Point :=
  (EuclideanGeometry.o.rotation t) p

/-- The horizontal, vertical and rotated vertical strips. -/
@[expose]
def strips (ω : ℝ) : Set Point × Set Point × Set Point :=
  let H : Set Point := {p | 0 ≤ p 1 ∧ p 1 ≤ 1}
  let V : Set Point := {p | 0 ≤ p 0 ∧ p 0 ≤ 1}
  (H, V, rotationMap (ω : Real.Angle) '' V)

/-- The intersection of strips and its two distinguished points. -/
@[expose]
def stripParallelogram (ω : ℝ) : Set Point × Point × Point :=
  ((strips ω).1 ∩ (strips ω).2.2, 0, !₂[Real.tan (Real.pi / 4 - ω / 2), 1])

/-- Corners, walls, rays and quadrants of a hallway. -/
structure HallwayParts where
  /-- The inner reentrant corner of the hallway. -/
  innerCorner : Point
  /-- The outer corner opposite the inner corner. -/
  outerCorner : Point
  /-- The outer wall corresponding to the fixed hallway’s line `x = 1`. -/
  a : Set Point
  /-- The inner wall corresponding to the fixed hallway’s line `x = 0`. -/
  b : Set Point
  /-- The outer wall corresponding to the fixed hallway’s line `y = 1`. -/
  c : Set Point
  /-- The inner wall corresponding to the fixed hallway’s line `y = 0`. -/
  d : Set Point
  /-- The ray on the inner B wall extending away from the corner. -/
  bRay : Set Point
  /-- The ray on the inner D wall extending away from the corner. -/
  dRay : Set Point
  /-- The closed quadrant cut out by the two outer walls. -/
  outerQuadrant : Set Point
  /-- The open forbidden quadrant behind the inner corner. -/
  innerQuadrant : Set Point

/-- The named parts of the fixed hallway. -/
@[expose]
def hallwayParts : HallwayParts where
  innerCorner := 0
  outerCorner := !₂[1, 1]
  a := {p | p 0 = 1}
  b := {p | p 0 = 0}
  c := {p | p 1 = 1}
  d := {p | p 1 = 0}
  bRay := {p | p 0 = 0 ∧ p 1 ≤ 0}
  dRay := {p | p 0 ≤ 0 ∧ p 1 = 0}
  outerQuadrant := {p | p 0 ≤ 1 ∧ p 1 ≤ 1}
  innerQuadrant := {p | p 0 < 0 ∧ p 1 < 0}

/-- Rotation followed by the support-determined translation. -/
@[expose]
def supportingPlacement (s : Set Point) (t : Real.Angle) (p : Point) : Point :=
  rotationMap t p + (supportValue s t - 1) • normalVector t +
    (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) • tangentVector t

/-- The supporting hallway of a nonempty compact set. -/
@[expose]
def supportingHallway (s : Set Point) (t : Real.Angle) : Set Point :=
  supportingPlacement s t '' hallway

/-- The images of all named hallway parts under its supporting placement. -/
@[expose]
def rotatingHallwayParts (s : Set Point) (t : Real.Angle) : HallwayParts where
  innerCorner := supportingPlacement s t hallwayParts.innerCorner
  outerCorner := supportingPlacement s t hallwayParts.outerCorner
  a := supportingPlacement s t '' hallwayParts.a
  b := supportingPlacement s t '' hallwayParts.b
  c := supportingPlacement s t '' hallwayParts.c
  d := supportingPlacement s t '' hallwayParts.d
  bRay := supportingPlacement s t '' hallwayParts.bRay
  dRay := supportingPlacement s t '' hallwayParts.dRay
  outerQuadrant := supportingPlacement s t '' hallwayParts.outerQuadrant
  innerQuadrant := supportingPlacement s t '' hallwayParts.innerQuadrant

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Hallway Parts
-/

public section

noncomputable section

namespace MovingSofa

theorem rightAngleRotation_apply (p : Point) :
    EuclideanGeometry.o.rightAngleRotation p = !₂[-p 1, p 0] := by
  apply (ext_inner_left (𝕜 := ℝ))
  intro y
  rw [Orientation.inner_rightAngleRotation_right, Orientation.areaForm_to_volumeForm,
    EuclideanGeometry.o.volumeForm_robust (EuclideanSpace.basisFun (Fin 2) ℝ) rfl,
    Module.Basis.det_apply]
  simp [Matrix.det_fin_two, Module.Basis.toMatrix, PiLp.inner_apply]
  ring

theorem inner_rotationMap_normalVector (p : Point) (t : Real.Angle) :
    inner ℝ (rotationMap t p) (normalVector t) = p 0 := by
  rw [rotationMap, Orientation.rotation_apply, rightAngleRotation_apply]
  simp [normalVector, frame, PiLp.inner_apply]
  linear_combination p 0 * Real.Angle.cos_sq_add_sin_sq t

theorem inner_rotationMap_tangentVector (p : Point) (t : Real.Angle) :
    inner ℝ (rotationMap t p) (tangentVector t) = p 1 := by
  rw [rotationMap, Orientation.rotation_apply, rightAngleRotation_apply]
  simp [tangentVector, frame, PiLp.inner_apply]
  linear_combination p 1 * Real.Angle.cos_sq_add_sin_sq t

theorem normalVector_add_pi_div_two (t : Real.Angle) :
    normalVector (t + ((Real.pi / 2 : ℝ) : Real.Angle)) = tangentVector t := by
  simp [normalVector, tangentVector, frame, Real.Angle.cos_add_pi_div_two,
    Real.Angle.sin_add_pi_div_two]

/-- Rotating a real normal direction by a right angle gives the tangent direction. -/
theorem normalVector_add_pi_div_two_real (t : ℝ) :
    normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle) = tangentVector (t : Real.Angle) := by
  rw [Real.Angle.coe_add, normalVector_add_pi_div_two]

theorem inner_supportingPlacement_normalVector (s : Set Point) (t : Real.Angle)
    (p : Point) :
    inner ℝ (supportingPlacement s t p) (normalVector t) =
      p 0 + supportValue s t - 1 := by
  simp only [supportingPlacement, inner_add_left, real_inner_smul_left,
    inner_rotationMap_normalVector]
  simp [normalVector, tangentVector, frame, PiLp.inner_apply,
    PiLp.norm_sq_eq_of_L2, Real.Angle.cos_sq_add_sin_sq]
  ring

theorem inner_supportingPlacement_tangentVector (s : Set Point) (t : Real.Angle)
    (p : Point) :
    inner ℝ (supportingPlacement s t p) (tangentVector t) =
      p 1 + supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1 := by
  simp only [supportingPlacement, inner_add_left, real_inner_smul_left,
    inner_rotationMap_tangentVector]
  simp [normalVector, tangentVector, frame, PiLp.inner_apply,
    PiLp.norm_sq_eq_of_L2, Real.Angle.cos_sq_add_sin_sq, add_comm]
  ring

theorem hallway_eq_outerQuadrant_sdiff_innerQuadrant :
    hallway = hallwayParts.outerQuadrant \ hallwayParts.innerQuadrant := by
  ext p
  constructor
  · rintro (⟨a, b, h, rfl⟩ | ⟨a, b, h, rfl⟩)
    · change (a ≤ 1 ∧ b ≤ 1) ∧ ¬(a < 0 ∧ b < 0)
      exact ⟨⟨h.1, h.2.2⟩, fun hn ↦ (not_lt_of_ge h.2.1) hn.2⟩
    · change (a ≤ 1 ∧ b ≤ 1) ∧ ¬(a < 0 ∧ b < 0)
      exact ⟨⟨h.2.1, h.2.2⟩, fun hn ↦ (not_lt_of_ge h.1) hn.1⟩
  · intro hp
    change (p 0 ≤ 1 ∧ p 1 ≤ 1) ∧ ¬(p 0 < 0 ∧ p 1 < 0) at hp
    have heq : (!₂[p 0, p 1] : Point) = p := by
      ext i
      fin_cases i <;> rfl
    by_cases h : 0 ≤ p 0
    · exact Or.inr ⟨p 0, p 1, ⟨h, hp.1.1, hp.1.2⟩, heq⟩
    · exact Or.inl ⟨p 0, p 1,
        ⟨hp.1.1, le_of_not_gt (fun hy ↦ hp.2 ⟨lt_of_not_ge h, hy⟩), hp.1.2⟩, heq⟩

/-- The first coordinate of a rotated point. -/
theorem rotationMap_apply_zero (θ : Real.Angle) (x : Point) :
    rotationMap θ x 0 = θ.cos * x 0 - θ.sin * x 1 := by
  rw [rotationMap, Orientation.rotation_apply, rightAngleRotation_apply]
  simp
  ring

/-- The second coordinate of a rotated point. -/
theorem rotationMap_apply_one (θ : Real.Angle) (x : Point) :
    rotationMap θ x 1 = θ.sin * x 0 + θ.cos * x 1 := by
  rw [rotationMap, Orientation.rotation_apply, rightAngleRotation_apply]
  simp
  ring

/-- Coordinate bounds for a point of the horizontal side of the hallway. -/
theorem mem_horizontalHallway_coordinates {p : Point} (hp : p ∈ horizontalHallway) :
    p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1 := by
  obtain ⟨x, y, h, rfl⟩ := hp
  simpa using h

/-- Coordinate bounds for a point of the vertical side of the hallway. -/
theorem mem_verticalHallway_coordinates {p : Point} (hp : p ∈ verticalHallway) :
    0 ≤ p 0 ∧ p 0 ≤ 1 ∧ p 1 ≤ 1 := by
  obtain ⟨x, y, h, rfl⟩ := hp
  simpa using h

/-- A point lies in the hallway exactly when it lies in the outer quadrant and is not
strictly inside the inner one. -/
theorem mem_hallway_iff (q : Point) : q ∈ hallway ↔
    (q 0 ≤ 1 ∧ q 1 ≤ 1) ∧ (0 ≤ q 0 ∨ 0 ≤ q 1) := by
  constructor
  · rintro (⟨a, b, h, rfl⟩ | ⟨a, b, h, rfl⟩)
    · exact ⟨⟨h.1, h.2.2⟩, Or.inr h.2.1⟩
    · exact ⟨⟨h.2.1, h.2.2⟩, Or.inl h.1⟩
  · rintro ⟨⟨hx, hy⟩, h⟩
    have heq : (!₂[q 0, q 1] : Point) = q := by
      ext i
      fin_cases i <;> rfl
    rcases h with hx0 | hy0
    · exact Or.inr ⟨q 0, q 1, ⟨hx0, hx, hy⟩, heq⟩
    · exact Or.inl ⟨q 0, q 1, ⟨hx, hy0, hy⟩, heq⟩

/-- Coordinate bounds place a point in the horizontal side of the hallway. -/
theorem mem_horizontalHallway_of_coordinates (p : Point)
    (hx : p 0 ≤ 1) (hy : p 1 ∈ Set.Icc (0 : ℝ) 1) : p ∈ horizontalHallway := by
  refine ⟨p 0, p 1, ⟨hx, hy⟩, ?_⟩
  ext i
  fin_cases i <;> rfl

/-- Coordinate bounds place a point in the vertical side of the hallway. -/
theorem mem_verticalHallway_of_coordinates (p : Point)
    (hx : p 0 ∈ Set.Icc (0 : ℝ) 1) (hy : p 1 ≤ 1) : p ∈ verticalHallway := by
  refine ⟨p 0, p 1, ⟨hx.1, hx.2, hy⟩, ?_⟩
  ext i
  fin_cases i <;> rfl

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Hallway Parts Properties
-/

public section

noncomputable section

namespace MovingSofa

/-- A supporting hallway lies in its outer quadrant. -/
theorem supportingHallway_subset_outerQuadrant (s : Set Point) (t : Real.Angle) :
    supportingHallway s t ⊆ (rotatingHallwayParts s t).outerQuadrant := by
  change supportingPlacement s t '' hallway ⊆
    supportingPlacement s t '' hallwayParts.outerQuadrant
  apply Set.image_mono
  rw [hallway_eq_outerQuadrant_sdiff_innerQuadrant]
  exact Set.sdiff_subset

theorem rotatingHallwayParts_formulas (s : Set Point) (t : Real.Angle) :
    supportingHallway s t = (rotatingHallwayParts s t).outerQuadrant \ (rotatingHallwayParts s
      t).innerQuadrant ∧
    (rotatingHallwayParts s t).innerCorner = (supportValue s t - 1) • normalVector t +
      (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) • tangentVector t ∧
    (rotatingHallwayParts s t).outerCorner = supportValue s t • normalVector t + supportValue s (t
      + ((Real.pi / 2 : ℝ) : Real.Angle)) • tangentVector t ∧
    (rotatingHallwayParts s t).a = normalLine t (supportValue s t) ∧
    (rotatingHallwayParts s t).b = normalLine t (supportValue s t - 1) ∧
    (rotatingHallwayParts s t).c = normalLine (t + ((Real.pi / 2 : ℝ) : Real.Angle)) (supportValue
      s (t + ((Real.pi / 2 : ℝ) : Real.Angle))) ∧
    (rotatingHallwayParts s t).d = normalLine (t + ((Real.pi / 2 : ℝ) : Real.Angle)) (supportValue
      s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) ∧
    (rotatingHallwayParts s t).outerQuadrant =
      normalHalfPlane t (supportValue s t) false false ∩
        normalHalfPlane (t + ((Real.pi / 2 : ℝ) : Real.Angle)) (supportValue s (t + ((Real.pi / 2
          : ℝ) : Real.Angle))) false false ∧
    (rotatingHallwayParts s t).innerQuadrant =
      normalHalfPlane t (supportValue s t - 1) false true ∩
        normalHalfPlane (t + ((Real.pi / 2 : ℝ) : Real.Angle)) (supportValue s (t + ((Real.pi / 2
          : ℝ) : Real.Angle)) - 1) false true := by
  have hinj : Function.Injective (supportingPlacement s t) := by
    intro p q h
    apply (EuclideanGeometry.o.rotation t).injective
    simpa only [supportingPlacement, rotationMap, add_left_inj] using h
  have hsurj : Function.Surjective (supportingPlacement s t) := by
    intro q
    obtain ⟨p, hp⟩ := (EuclideanGeometry.o.rotation t).surjective
      (q - (supportValue s t - 1) • normalVector t -
        (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) • tangentVector t)
    refine ⟨p, ?_⟩
    simp only [supportingPlacement, rotationMap, hp]
    abel
  have himage (A B : Set Point)
      (h : ∀ p, p ∈ A ↔ supportingPlacement s t p ∈ B) :
      supportingPlacement s t '' A = B := by
    apply (Set.preimage_eq_preimage hsurj).mp
    rw [Set.preimage_image_eq A hinj]
    exact Set.ext h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (Set.preimage_eq_preimage hsurj).mp
    change supportingPlacement s t ⁻¹' (supportingPlacement s t '' hallway) =
      supportingPlacement s t ⁻¹' (supportingPlacement s t '' hallwayParts.outerQuadrant \
        supportingPlacement s t '' hallwayParts.innerQuadrant)
    rw [Set.preimage_sdiff, Set.preimage_image_eq _ hinj,
      Set.preimage_image_eq _ hinj, Set.preimage_image_eq _ hinj]
    exact hallway_eq_outerQuadrant_sdiff_innerQuadrant
  · simp [rotatingHallwayParts, supportingPlacement, hallwayParts, rotationMap]
  · simp only [rotatingHallwayParts, supportingPlacement, hallwayParts,
      rotationMap, Orientation.rotation_apply, rightAngleRotation_apply]
    ext i
    fin_cases i <;> simp [normalVector, tangentVector, frame] <;> ring
  · apply himage
    intro p
    change p 0 = 1 ↔ inner ℝ (supportingPlacement s t p) (normalVector t) = _
    rw [inner_supportingPlacement_normalVector]
    constructor <;> intro h <;> linarith
  · apply himage
    intro p
    change p 0 = 0 ↔ inner ℝ (supportingPlacement s t p) (normalVector t) = _
    rw [inner_supportingPlacement_normalVector]
    constructor <;> intro h <;> linarith
  · apply himage
    intro p
    change p 1 = 1 ↔ inner ℝ (supportingPlacement s t p)
      (normalVector (t + ((Real.pi / 2 : ℝ) : Real.Angle))) = _
    rw [normalVector_add_pi_div_two, inner_supportingPlacement_tangentVector]
    constructor <;> intro h <;> linarith
  · apply himage
    intro p
    change p 1 = 0 ↔ inner ℝ (supportingPlacement s t p)
      (normalVector (t + ((Real.pi / 2 : ℝ) : Real.Angle))) = _
    rw [normalVector_add_pi_div_two, inner_supportingPlacement_tangentVector]
    constructor <;> intro h <;> linarith
  · apply himage
    intro p
    change (p 0 ≤ 1 ∧ p 1 ≤ 1) ↔
      (inner ℝ (supportingPlacement s t p) (normalVector t) ≤ _) ∧
      (inner ℝ (supportingPlacement s t p)
        (normalVector (t + ((Real.pi / 2 : ℝ) : Real.Angle))) ≤ _)
    rw [normalVector_add_pi_div_two, inner_supportingPlacement_normalVector,
      inner_supportingPlacement_tangentVector]
    constructor <;> rintro ⟨h₀, h₁⟩ <;> constructor <;> linarith
  · apply himage
    intro p
    change (p 0 < 0 ∧ p 1 < 0) ↔
      (inner ℝ (supportingPlacement s t p) (normalVector t) < _) ∧
      (inner ℝ (supportingPlacement s t p)
        (normalVector (t + ((Real.pi / 2 : ℝ) : Real.Angle))) < _)
    rw [normalVector_add_pi_div_two, inner_supportingPlacement_normalVector,
      inner_supportingPlacement_tangentVector]
    constructor <;> rintro ⟨h₀, h₁⟩ <;> constructor <;> linarith

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Hallway Ray
-/

public section

noncomputable section

open Set MeasureTheory

namespace MovingSofa

/-- Coordinate description of the downward ray of a supporting hallway. -/
theorem mem_rotatingHallwayParts_bRay_iff (s : Set Point) (t : Real.Angle) (p : Point) :
    p ∈ (rotatingHallwayParts s t).bRay ↔
      inner ℝ p (normalVector t) = supportValue s t - 1 ∧
      inner ℝ p (tangentVector t) ≤
        supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1 := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    change q 0 = 0 ∧ q 1 ≤ 0 at hq
    rw [inner_supportingPlacement_normalVector, inner_supportingPlacement_tangentVector]
    exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
  · intro hp
    obtain ⟨q, rfl⟩ := (show Function.Surjective (supportingPlacement s t) by
      intro p
      obtain ⟨q, hq⟩ := (EuclideanGeometry.o.rotation t).surjective
        (p - (supportValue s t - 1) • normalVector t -
          (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) • tangentVector t)
      refine ⟨q, ?_⟩
      simp only [supportingPlacement, rotationMap, hq]
      abel) p
    rw [inner_supportingPlacement_normalVector, inner_supportingPlacement_tangentVector] at hp
    change supportingPlacement s t q ∈ supportingPlacement s t '' hallwayParts.bRay
    refine ⟨q, ?_, rfl⟩
    change q 0 = 0 ∧ q 1 ≤ 0
    exact ⟨by linarith [hp.1], by linarith [hp.2]⟩

/-- Coordinate description of the leftward ray of a supporting hallway. -/
theorem mem_rotatingHallwayParts_dRay_iff (s : Set Point) (t : Real.Angle) (p : Point) :
    p ∈ (rotatingHallwayParts s t).dRay ↔
      inner ℝ p (normalVector t) ≤ supportValue s t - 1 ∧
      inner ℝ p (tangentVector t) =
        supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1 := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    change q 0 ≤ 0 ∧ q 1 = 0 at hq
    rw [inner_supportingPlacement_normalVector, inner_supportingPlacement_tangentVector]
    exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
  · intro hp
    obtain ⟨q, rfl⟩ := (show Function.Surjective (supportingPlacement s t) by
      intro p
      obtain ⟨q, hq⟩ := (EuclideanGeometry.o.rotation t).surjective
        (p - (supportValue s t - 1) • normalVector t -
          (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) • tangentVector t)
      refine ⟨q, ?_⟩
      simp only [supportingPlacement, rotationMap, hq]
      abel) p
    rw [inner_supportingPlacement_normalVector, inner_supportingPlacement_tangentVector] at hp
    change supportingPlacement s t q ∈ supportingPlacement s t '' hallwayParts.dRay
    refine ⟨q, ?_, rfl⟩
    change q 0 ≤ 0 ∧ q 1 = 0
    exact ⟨by linarith [hp.1], by linarith [hp.2]⟩

/-- The part of a supporting hallway ray above a transverse line has the expected length. -/
theorem hausdorffMeasure_bRay_inter_normalHalfPlane (s : Set Point) (t u h : ℝ)
    (htrans : 0 < inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (u : Real.Angle))) :
    Measure.hausdorffMeasure 1
        ((rotatingHallwayParts s (t : Real.Angle)).bRay ∩
          normalHalfPlane (u : Real.Angle) h true false) =
      ENNReal.ofReal (max 0
        ((inner ℝ (rotatingHallwayParts s (t : Real.Angle)).innerCorner
          (normalVector (u : Real.Angle)) - h) /
          inner ℝ (tangentVector (t : Real.Angle)) (normalVector (u : Real.Angle)))) := by
  let x := (rotatingHallwayParts s (t : Real.Angle)).innerCorner
  let v := tangentVector (t : Real.Angle)
  let d := inner ℝ v (normalVector (u : Real.Angle))
  let α := (inner ℝ x (normalVector (u : Real.Angle)) - h) / d
  have hd : 0 < d := htrans
  have hxn : inner ℝ x (normalVector (t : Real.Angle)) =
      supportValue s (t : Real.Angle) - 1 := by
    change inner ℝ (supportingPlacement s (t : Real.Angle) (0 : Point))
      (normalVector (t : Real.Angle)) = _
    rw [inner_supportingPlacement_normalVector]
    simp
  have hxt : inner ℝ x v =
      supportValue s ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1 := by
    change inner ℝ (supportingPlacement s (t : Real.Angle) (0 : Point))
      (tangentVector (t : Real.Angle)) = _
    rw [inner_supportingPlacement_tangentVector]
    simp only [PiLp.zero_apply]
    ring
  have hvn : inner ℝ v (normalVector (t : Real.Angle)) = 0 := by
    rw [real_inner_comm, inner_normalVector_tangentVector]
  have hvv : inner ℝ v v = 1 := inner_tangentVector_self t
  have hpoint (p : Point) (lam : ℝ)
      (hn : inner ℝ p (normalVector (t : Real.Angle)) =
        inner ℝ x (normalVector (t : Real.Angle)))
      (ht : inner ℝ p v = inner ℝ x v - lam) : p = x - lam • v := by
    rw [← inner_normalVector_smul_add_inner_tangentVector_smul p (t : Real.Angle),
      ← inner_normalVector_smul_add_inner_tangentVector_smul x (t : Real.Angle)]
    rw [hn, ht]
    module
  by_cases hα : 0 ≤ α
  · have hset : (rotatingHallwayParts s (t : Real.Angle)).bRay ∩
        normalHalfPlane (u : Real.Angle) h true false = segment ℝ x (x - α • v) := by
      ext p
      change (p ∈ (rotatingHallwayParts s (t : Real.Angle)).bRay ∧
        h ≤ inner ℝ p (normalVector (u : Real.Angle))) ↔ _
      constructor
      · rintro ⟨hray, hu⟩
        rw [mem_rotatingHallwayParts_bRay_iff] at hray
        let lam := inner ℝ x v - inner ℝ p v
        have hlam0 : 0 ≤ lam := by dsimp [lam]; rw [hxt]; linarith [hray.2]
        have hp : p = x - lam • v := by
          apply hpoint p lam
          · rw [hray.1, hxn]
          · dsimp [lam]
            ring
        have hlamα : lam ≤ α := by
          rw [hp, inner_sub_left, real_inner_smul_left] at hu
          apply (le_div_iff₀ hd).2
          dsimp [d]
          nlinarith
        by_cases hα0 : α = 0
        · have : lam = 0 := le_antisymm (hα0 ▸ hlamα) hlam0
          simp [hα0, hp, this]
        · rw [segment_eq_image]
          refine ⟨lam / α,
            ⟨div_nonneg hlam0 hα, (div_le_one (lt_of_le_of_ne hα ?_)).2 hlamα⟩, ?_⟩
          · exact Ne.symm hα0
          · change (1 - lam / α) • x + (lam / α) • (x - α • v) = p
            rw [hp]
            rw [smul_sub, smul_smul, div_mul_cancel₀ _ hα0]
            module
      · intro hp
        rw [segment_eq_image] at hp
        obtain ⟨r, hr, rfl⟩ := hp
        have heq : (1 - r) • x + r • (x - α • v) = x - (r * α) • v := by module
        rw [show (fun θ : ℝ ↦ (1 - θ) • x + θ • (x - α • v)) r =
          x - (r * α) • v from heq]
        constructor
        · rw [mem_rotatingHallwayParts_bRay_iff]
          constructor
          · simp only [inner_sub_left, real_inner_smul_left, hvn, mul_zero, sub_zero, hxn]
          · simp only [inner_sub_left, real_inner_smul_left]
            change inner ℝ x v - r * α * inner ℝ v v ≤ _
            rw [hvv, mul_one, hxt]
            nlinarith [mul_nonneg hr.1 hα]
        · simp only [inner_sub_left, real_inner_smul_left]
          have hrα : r * α ≤ α := by nlinarith [hr.1, hr.2, hα]
          have hαeq : inner ℝ x (normalVector (u : Real.Angle)) - h = α * d := by
            dsimp [α]
            rw [div_mul_cancel₀ _ hd.ne']
          dsimp [d] at hαeq ⊢
          nlinarith
    rw [hset, MeasureTheory.hausdorffMeasure_segment, edist_dist, dist_eq_norm]
    have hvnorm : ‖v‖ = 1 := by
      dsimp [v]
      rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
      rw [EuclideanSpace.norm_sq_eq]
      simp [tangentVector, frame, Fin.sum_univ_two, Real.sin_sq_add_cos_sq]
    have hsub : x - (x - α • v) = α • v := by module
    rw [hsub, norm_smul, hvnorm, mul_one]
    simp only [Real.norm_eq_abs, abs_of_nonneg hα]
    simp only [x, v, d, α, max_eq_right hα]
  · have hset : (rotatingHallwayParts s (t : Real.Angle)).bRay ∩
        normalHalfPlane (u : Real.Angle) h true false = ∅ := by
      ext p
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hp
      change p ∈ (rotatingHallwayParts s (t : Real.Angle)).bRay ∧
        h ≤ inner ℝ p (normalVector (u : Real.Angle)) at hp
      rw [mem_rotatingHallwayParts_bRay_iff] at hp
      let lam := inner ℝ x v - inner ℝ p v
      have hlam0 : 0 ≤ lam := by dsimp [lam]; rw [hxt]; linarith [hp.1.2]
      have hp' : p = x - lam • v := by
        apply hpoint p lam
        · rw [hp.1.1, hxn]
        · dsimp [lam]
          ring
      have hlamα : lam ≤ α := by
        have hu := hp.2
        rw [hp', inner_sub_left, real_inner_smul_left] at hu
        apply (le_div_iff₀ hd).2
        dsimp [d]
        nlinarith
      linarith
    rw [hset]
    have hα' : α ≤ 0 := le_of_not_ge hα
    simp only [measure_empty, ENNReal.ofReal_zero, x, v, d, α, max_eq_left hα']

/-- A planar set on one line of a moving frame, with bounded tangent coordinate, is short. -/
theorem hausdorffMeasure_le_of_frame_bounds {S : Set Point} {t e lo hi : ℝ}
    (hS : ∀ p ∈ S, inner ℝ p (normalVector (t : Real.Angle)) = e ∧
      lo ≤ inner ℝ p (tangentVector (t : Real.Angle)) ∧
      inner ℝ p (tangentVector (t : Real.Angle)) ≤ hi) :
    Measure.hausdorffMeasure 1 S ≤ ENNReal.ofReal (max 0 (hi - lo)) := by
  have hvv : inner ℝ (tangentVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = 1 :=
    inner_tangentVector_self t
  have hnorm : ‖tangentVector (t : Real.Angle)‖ = 1 := by
    have h := real_inner_self_eq_norm_mul_norm (tangentVector (t : Real.Angle))
    rw [hvv] at h
    nlinarith [norm_nonneg (tangentVector (t : Real.Angle))]
  have hsub : S ⊆ segment ℝ
      (e • normalVector (t : Real.Angle) + lo • tangentVector (t : Real.Angle))
      (e • normalVector (t : Real.Angle) + max lo hi • tangentVector (t : Real.Angle)) := by
    intro p hp
    obtain ⟨hpn, hplo, hphi⟩ := hS p hp
    obtain ⟨y, hy⟩ : ∃ y : ℝ, inner ℝ p (tangentVector (t : Real.Angle)) = y := ⟨_, rfl⟩
    rw [hy] at hplo hphi
    have hdecomp : p = e • normalVector (t : Real.Angle) + y • tangentVector (t : Real.Angle) := by
      conv_lhs => rw [← inner_normalVector_smul_add_inner_tangentVector_smul p (t : Real.Angle)]
      rw [hpn, hy]
    have hym : y ≤ max lo hi := hphi.trans (le_max_right lo hi)
    rcases le_or_gt (max lo hi) lo with hml | hml
    · have hylo : y = lo := le_antisymm (hym.trans hml) hplo
      rw [hdecomp, hylo]
      exact left_mem_segment ℝ _ _
    · rw [segment_eq_image]
      refine ⟨(y - lo) / (max lo hi - lo),
        ⟨div_nonneg (by linarith) (by linarith), ?_⟩, ?_⟩
      · rw [div_le_one (by linarith)]
        linarith
      · have hθ : lo + (y - lo) / (max lo hi - lo) * (max lo hi - lo) = y := by
          field_simp
          ring
        have hexp : (1 - (y - lo) / (max lo hi - lo)) •
              (e • normalVector (t : Real.Angle) + lo • tangentVector (t : Real.Angle)) +
            ((y - lo) / (max lo hi - lo)) •
              (e • normalVector (t : Real.Angle) +
                max lo hi • tangentVector (t : Real.Angle)) =
            e • normalVector (t : Real.Angle) +
              (lo + (y - lo) / (max lo hi - lo) * (max lo hi - lo)) •
                tangentVector (t : Real.Angle) := by
          module
        change (1 - (y - lo) / (max lo hi - lo)) •
              (e • normalVector (t : Real.Angle) + lo • tangentVector (t : Real.Angle)) +
            ((y - lo) / (max lo hi - lo)) •
              (e • normalVector (t : Real.Angle) +
                max lo hi • tangentVector (t : Real.Angle)) = p
        rw [hexp, hθ]
        exact hdecomp.symm
  refine (measure_mono hsub).trans (le_of_eq ?_)
  rw [MeasureTheory.hausdorffMeasure_segment, edist_dist, dist_eq_norm]
  congr 1
  have hdiff : e • normalVector (t : Real.Angle) + lo • tangentVector (t : Real.Angle) -
      (e • normalVector (t : Real.Angle) + max lo hi • tangentVector (t : Real.Angle)) =
      (lo - max lo hi) • tangentVector (t : Real.Angle) := by module
  rw [hdiff, norm_smul, hnorm, mul_one, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr (le_max_left lo hi)), neg_sub]
  rcases le_total hi lo with hle | hle
  · rw [max_eq_left hle, max_eq_left (by linarith), sub_self]
  · rw [max_eq_right hle, max_eq_right (by linarith)]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Hallway Support
-/

public section

noncomputable section

namespace MovingSofa

theorem outerCorner_eq_support_sum (K : ConvexBody Point) (t : ℝ) :
    (rotatingHallwayParts (K : Set Point) (t : Real.Angle)).outerCorner =
      supportValue K (t : Real.Angle) • normalVector (t : Real.Angle) +
      supportValue K ((t + Real.pi / 2 : ℝ) : Real.Angle) • tangentVector (t : Real.Angle) := by
  have hrot : rotationMap (t : Real.Angle) (!₂[1, 1] : Point) =
      normalVector (t : Real.Angle) + tangentVector (t : Real.Angle) := by
    unfold rotationMap
    rw [Orientation.rotation_apply, rightAngleRotation_apply]
    ext i
    fin_cases i <;> simp [normalVector, tangentVector, frame]
    ring
  simp only [rotatingHallwayParts, supportingPlacement, hallwayParts, hrot, Real.Angle.coe_add]
  module

/-- Two supporting lines at angular difference exactly `π / 2` meet at the outer corner of the
rotating supporting hallway. -/
theorem supportingIntersection_add_pi_div_two_eq_outerCorner (K : ConvexBody Point) (t : ℝ) :
    supportingIntersection K (t : Real.Angle) ((t + Real.pi / 2 : ℝ) : Real.Angle) =
      (rotatingHallwayParts (K : Set Point) (t : Real.Angle)).outerCorner := by
  have hd : ((t + Real.pi / 2 : ℝ) : Real.Angle) - (t : Real.Angle) =
      ((Real.pi / 2 : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_sub, show t + Real.pi / 2 - t = Real.pi / 2 from by ring]
  rw [supportingIntersection, hd, Real.Angle.cos_coe, Real.Angle.sin_coe, Real.cos_pi_div_two,
    Real.sin_pi_div_two, outerCorner_eq_support_sum]
  simp only [mul_zero, sub_zero, div_one]

/-- The outer corner of the rotating supporting hallway is its inner corner translated by the
frame sum `u_t + v_t`. -/
theorem outerCorner_eq_innerCorner_add (K : ConvexBody Point) (t : ℝ) :
    (rotatingHallwayParts (K : Set Point) (t : Real.Angle)).outerCorner =
      (rotatingHallwayParts (K : Set Point) (t : Real.Angle)).innerCorner +
        (normalVector (t : Real.Angle) + tangentVector (t : Real.Angle)) := by
  rw [outerCorner_eq_support_sum]
  simp only [rotatingHallwayParts, hallwayParts, supportingPlacement, rotationMap,
    map_zero, zero_add, Real.Angle.coe_add]
  module

theorem continuous_outerCorner (K : ConvexBody Point) :
    Continuous
      (fun s : ℝ ↦ (rotatingHallwayParts (K : Set Point) (s : Real.Angle)).outerCorner) := by
  simp_rw [outerCorner_eq_support_sum]
  exact ((continuous_supportValue_real K).smul continuous_normalVector_real).add
    (((continuous_supportValue_real K).comp (continuous_id.add_const _)).smul
      (continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_tangentVector t).continuousAt))

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Parallelogram
-/

public section

noncomputable section

namespace MovingSofa

/-- The strip intersection is described by its vertical and rotated coordinates. -/
theorem mem_stripParallelogram_iff (ω : ℝ) (p : Point) :
    p ∈ (stripParallelogram ω).1 ↔
      (0 ≤ p 1 ∧ p 1 ≤ 1) ∧
      (0 ≤ inner ℝ p (normalVector (ω : Real.Angle)) ∧
        inner ℝ p (normalVector (ω : Real.Angle)) ≤ 1) := by
  change ((0 ≤ p 1 ∧ p 1 ≤ 1) ∧
    p ∈ rotationMap (ω : Real.Angle) '' {q : Point | 0 ≤ q 0 ∧ q 0 ≤ 1}) ↔ _
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa only [inner_rotationMap_normalVector, Set.mem_ofPred_eq] using hq
  · intro hp
    obtain ⟨q, rfl⟩ := (EuclideanGeometry.o.rotation (ω : Real.Angle)).surjective p
    change 0 ≤ inner ℝ (rotationMap (ω : Real.Angle) q)
        (normalVector (ω : Real.Angle)) ∧
      inner ℝ (rotationMap (ω : Real.Angle) q) (normalVector (ω : Real.Angle)) ≤ 1 at hp
    exact ⟨q, by
      simpa only [inner_rotationMap_normalVector, Set.mem_ofPred_eq] using hp, rfl⟩

/-- Projection on the downward unit normal negates the vertical coordinate. -/
theorem inner_normalVector_three_pi_div_two (p : Point) :
    inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) = -p 1 := by
  simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
    show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring, Real.cos_add, Real.sin_add,
    -Real.Angle.coe_add]

/-- The horizontal coordinate is the projection on the normal at angle zero. -/
theorem inner_normalVector_zero (p : Point) :
    inner ℝ p (normalVector ((0 : ℝ) : Real.Angle)) = p 0 := by
  simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]

/-- The vertical coordinate is the projection on the tangent at angle zero. -/
theorem inner_tangentVector_zero (p : Point) :
    inner ℝ p (tangentVector ((0 : ℝ) : Real.Angle)) = p 1 := by
  simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]

/-- The vertical coordinate is the projection on the upward unit normal. -/
theorem inner_normalVector_pi_div_two (p : Point) :
    inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = p 1 := by
  simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]

/-- Projection on the leftward tangent at a right angle negates the horizontal coordinate. -/
theorem inner_tangentVector_pi_div_two (p : Point) :
    inner ℝ p (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) = -p 0 := by
  simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]

/-- Projection on the leftward tangent at the straight angle negates the vertical coordinate. -/
theorem inner_tangentVector_pi (p : Point) :
    inner ℝ p (tangentVector ((Real.pi : ℝ) : Real.Angle)) = -p 1 := by
  simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]

/-- The projection of a multiple of the horizontal normal on another unit normal. -/
theorem inner_smul_normalVector_zero (x t : ℝ) :
    inner ℝ (x • normalVector (0 : Real.Angle)) (normalVector (t : Real.Angle)) =
      x * Real.cos t := by
  simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- The horizontal bottom of the strip intersection has zero downward support. -/
theorem supportValue_stripParallelogram_bottom (ω : ℝ) :
    supportValue (stripParallelogram ω).1 ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
  have hzero : (0 : Point) ∈ (stripParallelogram ω).1 := by
    rw [mem_stripParallelogram_iff]
    simp
  have hbound : ∀ y ∈ (fun p ↦ inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle))) ''
      (stripParallelogram ω).1, y ≤ 0 := by
    rintro y ⟨p, hp, rfl⟩
    dsimp only
    rw [inner_normalVector_three_pi_div_two]
    exact neg_nonpos.mpr ((mem_stripParallelogram_iff ω p).1 hp).1.1
  have hmem : (0 : ℝ) ∈ (fun p ↦ inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle))) ''
      (stripParallelogram ω).1 := ⟨0, hzero, by simp⟩
  exact le_antisymm (csSup_le ⟨0, hmem⟩ hbound) (le_csSup ⟨0, hbound⟩ hmem)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Parallelogram Gap
-/

public section

noncomputable section

namespace MovingSofa

theorem parallelogram_gap (ω : ℝ) (hω : ω ∈ Set.Ico 0 (Real.pi / 2)) :
    (stripParallelogram ω).2.2 - tangentVector 0 =
      Real.tan ((Real.pi / 2 - ω) / 2) • normalVector 0 ∧
    (stripParallelogram ω).2.2 - normalVector (ω : Real.Angle) =
      Real.tan ((Real.pi / 2 - ω) / 2) • tangentVector (ω : Real.Angle) ∧
    (stripParallelogram ω).1 ∩
        (supportingLineHalfPlane (stripParallelogram ω).1
          ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1 =
      segment ℝ (0 : Point) ((Real.cos ω)⁻¹ • normalVector 0) ∧
    normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ∩
        normalLine (ω : Real.Angle) 1 =
      {((Real.cos ω)⁻¹ • normalVector 0 : Point)} ∧
    Real.tan ((Real.pi / 2 - ω) / 2) = (Real.cos ω)⁻¹ - Real.tan ω := by
  have hcos : 0 < Real.cos ω :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hω.1], hω.2⟩
  have hgap := Real.tan_pi_div_two_sub_div_two ω hω
  have hfirst : (stripParallelogram ω).2.2 - tangentVector 0 =
      Real.tan ((Real.pi / 2 - ω) / 2) • normalVector 0 := by
    ext i
    fin_cases i <;> simp [stripParallelogram, normalVector, tangentVector, frame]
    ring_nf
  have hsecond : (stripParallelogram ω).2.2 - normalVector (ω : Real.Angle) =
      Real.tan ((Real.pi / 2 - ω) / 2) • tangentVector (ω : Real.Angle) := by
    have harg : Real.pi / 4 - ω / 2 = (Real.pi / 2 - ω) / 2 := by ring
    have hc : Real.tan ((Real.pi / 2 - ω) / 2) * Real.cos ω = 1 - Real.sin ω := by
      rw [hgap, Real.tan_eq_sin_div_cos]
      field_simp [hcos.ne']
    have hc' : Real.tan ((Real.pi / 2 - ω) / 2) * (1 + Real.sin ω) =
        Real.cos ω := by
      rw [hgap, Real.tan_eq_sin_div_cos]
      field_simp [hcos.ne']
      nlinarith [Real.sin_sq_add_cos_sq ω]
    ext i
    fin_cases i <;>
      simp [stripParallelogram, normalVector, tangentVector, frame, harg] <;> nlinarith
  have hedge : (stripParallelogram ω).1 ∩
        (supportingLineHalfPlane (stripParallelogram ω).1
          ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1 =
      segment ℝ (0 : Point) ((Real.cos ω)⁻¹ • normalVector 0) := by
    rw [supportingLineHalfPlane, supportValue_stripParallelogram_bottom]
    ext p
    simp only [Set.mem_inter_iff, mem_stripParallelogram_iff, normalLine,
      Set.mem_ofPred_eq, segment_eq_image, Set.mem_image, Set.mem_Icc]
    rw [inner_normalVector_three_pi_div_two]
    constructor
    · rintro ⟨⟨⟨hp₀, hp₁⟩, hq₀, hq₁⟩, hbottom⟩
      have hpzero : p 1 = 0 := by linarith
      have hx₀ : 0 ≤ p 0 * Real.cos ω := by
        simpa [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two, hpzero,
          mul_comm] using hq₀
      have hx₁ : p 0 * Real.cos ω ≤ 1 := by
        simpa [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two, hpzero,
          mul_comm] using hq₁
      refine ⟨p 0 * Real.cos ω, ⟨hx₀, hx₁⟩, ?_⟩
      ext i
      fin_cases i <;> simp [normalVector, frame, hpzero, hcos.ne']
    · rintro ⟨x, hx, rfl⟩
      have hinner : inner ℝ (x • (Real.cos ω)⁻¹ • normalVector 0)
          (normalVector (ω : Real.Angle)) = x := by
        simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
        field_simp [hcos.ne']
      constructor
      · exact ⟨by simp [normalVector, frame], by simpa [hinner] using hx⟩
      · simp [normalVector, frame]
  have hintersection : normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ∩
        normalLine (ω : Real.Angle) 1 =
      {((Real.cos ω)⁻¹ • normalVector 0 : Point)} := by
    ext p
    simp only [Set.mem_inter_iff, normalLine, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hvertical, hrotated⟩
      have hpone : p 1 = 0 := by
        simpa [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] using hvertical
      have hpzero : p 0 * Real.cos ω = 1 := by
        simpa [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two, hpone,
          mul_comm] using hrotated
      ext i
      fin_cases i
      · simp [normalVector, frame]
        field_simp [hcos.ne']
        exact hpzero
      · simp [normalVector, frame, hpone]
    · intro hp
      rw [hp]
      constructor
      · simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
      · simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
        field_simp [hcos.ne']
  exact ⟨hfirst, hsecond, hedge, hintersection, hgap⟩

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Path Half Plane Cap
-/

public section

noncomputable section

namespace MovingSofa

/-- The set satisfying the horizontal base and all upper support constraints of a path. -/
@[expose]
def outerPathConstraintSet (x : Set.Icc (0 : ℝ) (Real.pi / 2) → Point) : Set Point :=
  {q | 0 ≤ q 1 ∧ ∀ t,
    inner ℝ q (normalVector (t.val : Real.Angle)) ≤
      inner ℝ (x t) (normalVector (t.val : Real.Angle)) + 1 ∧
    inner ℝ q (tangentVector (t.val : Real.Angle)) ≤
      inner ℝ (x t) (tangentVector (t.val : Real.Angle)) + 1}

theorem outerPathConstraintSet_isCap
    (x : Set.Icc (0 : ℝ) (Real.pi / 2) → Point)
    (hx : x ⟨0, le_rfl, by positivity⟩ = 0)
    (hbottom : ∃ p ∈ outerPathConstraintSet x, p 1 = 0)
    (htop : ∃ p ∈ outerPathConstraintSet x, p 1 = 1) :
    ∃ K : ConvexBody Point, (K : Set Point) = outerPathConstraintSet x ∧
      IsCap (Real.pi / 2) K := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hxO : x ⟨0, le_rfl, hpi⟩ = 0 := hx
  -- half-plane representation with cap-admissible normals
  obtain ⟨C, hCnormals, hrep⟩ :
      ∃ C : Set (Real.Angle × ℝ),
        (∀ c ∈ C, c.1 ∈ ((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles (Real.pi / 2)) ∪
          capLowerNormals (Real.pi / 2)) ∧
        outerPathConstraintSet x = ⋂ c ∈ C, normalHalfPlane c.1 c.2 false false := by
    refine ⟨{(((3 * Real.pi / 2 : ℝ) : Real.Angle), (0 : ℝ))} ∪
      ((Set.range fun t : Set.Icc (0 : ℝ) (Real.pi / 2) ↦
          (((t.val : ℝ) : Real.Angle),
            inner ℝ (x t) (normalVector ((t.val : ℝ) : Real.Angle)) + 1)) ∪
        (Set.range fun t : Set.Icc (0 : ℝ) (Real.pi / 2) ↦
          (((t.val + Real.pi / 2 : ℝ) : Real.Angle),
            inner ℝ (x t) (tangentVector ((t.val : ℝ) : Real.Angle)) + 1))), ?_, ?_⟩
    · rintro c (rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl ⟨t.val, Or.inl ⟨t.2.1, t.2.2⟩, rfl⟩
      · exact Or.inl ⟨t.val + Real.pi / 2,
          Or.inr ⟨by linarith [t.2.1], by linarith [t.2.2]⟩, rfl⟩
    · ext q
      simp only [Set.mem_iInter, Set.mem_union, Set.mem_singleton_iff, Set.mem_range]
      constructor
      · rintro ⟨hq0, hqt⟩ c (rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩)
        · change inner ℝ q (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤ 0
          rw [inner_normalVector_three_pi_div_two]
          linarith
        · exact (hqt t).1
        · change inner ℝ q (normalVector ((t.val + Real.pi / 2 : ℝ) : Real.Angle)) ≤ _
          rw [normalVector_add_pi_div_two_real]
          exact (hqt t).2
      · intro hq
        refine ⟨?_, fun t ↦ ⟨?_, ?_⟩⟩
        · have h : inner ℝ q (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤ 0 :=
            hq _ (Or.inl rfl)
          rw [inner_normalVector_three_pi_div_two] at h
          linarith
        · exact hq _ (Or.inr (Or.inl ⟨t, rfl⟩))
        · have h : inner ℝ q (normalVector ((t.val + Real.pi / 2 : ℝ) : Real.Angle)) ≤
              inner ℝ (x t) (tangentVector ((t.val : ℝ) : Real.Angle)) + 1 :=
            hq _ (Or.inr (Or.inr ⟨t, rfl⟩))
          rwa [normalVector_add_pi_div_two_real] at h
  -- the constraints at the two endpoints confine the set to a bounded rectangle
  have hxbox : ∀ q ∈ outerPathConstraintSet x,
      x ⟨Real.pi / 2, hpi, le_rfl⟩ 0 - 1 ≤ q 0 ∧ q 0 ≤ 1 ∧ 0 ≤ q 1 ∧ q 1 ≤ 1 := by
    rintro q ⟨hq0, hqt⟩
    have h0n : inner ℝ q (normalVector ((0 : ℝ) : Real.Angle)) ≤
        inner ℝ (x ⟨0, le_rfl, hpi⟩) (normalVector ((0 : ℝ) : Real.Angle)) + 1 :=
      (hqt ⟨0, le_rfl, hpi⟩).1
    have h0t : inner ℝ q (tangentVector ((0 : ℝ) : Real.Angle)) ≤
        inner ℝ (x ⟨0, le_rfl, hpi⟩) (tangentVector ((0 : ℝ) : Real.Angle)) + 1 :=
      (hqt ⟨0, le_rfl, hpi⟩).2
    have hTt : inner ℝ q (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤
        inner ℝ (x ⟨Real.pi / 2, hpi, le_rfl⟩)
          (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) + 1 :=
      (hqt ⟨Real.pi / 2, hpi, le_rfl⟩).2
    rw [hxO, inner_zero_left, inner_normalVector_zero] at h0n
    rw [hxO, inner_zero_left, inner_tangentVector_zero] at h0t
    rw [inner_tangentVector_pi_div_two, inner_tangentVector_pi_div_two] at hTt
    exact ⟨by linarith, by linarith, hq0, by linarith⟩
  obtain ⟨pb, hpb, hpb1⟩ := hbottom
  obtain ⟨pt, hpt, hpt1⟩ := htop
  obtain ⟨K, hKset⟩ : ∃ K : ConvexBody Point, (K : Set Point) = outerPathConstraintSet x := by
    refine ⟨{ carrier := outerPathConstraintSet x
              convex' := ?_
              isCompact' := ?_
              nonempty' := ⟨pb, hpb⟩ }, rfl⟩
    · rw [hrep]
      exact convex_iInter fun c ↦ convex_iInter fun _ ↦ convex_normalHalfPlane c.1 c.2 false
    · refine Metric.isCompact_iff_isClosed_bounded.2 ⟨?_, ?_⟩
      · rw [hrep]
        exact isClosed_iInter fun c ↦ isClosed_iInter fun _ ↦
          isClosed_normalHalfPlane c.1 c.2 false
      · refine (EuclideanSpace.isBounded_coordinate_rectangle
          (x ⟨Real.pi / 2, hpi, le_rfl⟩ 0 - 1) 1 0 1).subset fun q hq ↦ ?_
        obtain ⟨h1, h2, h3, h4⟩ := hxbox q hq
        exact ⟨h1, h2, h3, h4⟩
  -- the strip inclusion and the two contacts fix the four normalized support values
  have hsvTop : supportValue (K : Set Point) ((Real.pi / 2 : ℝ) : Real.Angle) = 1 := by
    refine le_antisymm (supportValue_le_of_subset_normalHalfPlane K _ 1 fun q hq ↦ ?_) ?_
    · change inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤ 1
      rw [inner_normalVector_pi_div_two]
      rw [hKset] at hq
      exact (hxbox q hq).2.2.2
    · have h := inner_le_supportValue K (hKset ▸ hpt) ((Real.pi / 2 : ℝ) : Real.Angle)
      rwa [inner_normalVector_pi_div_two, hpt1] at h
  have hsvBot : supportValue (K : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    refine le_antisymm (supportValue_le_of_subset_normalHalfPlane K _ 0 fun q hq ↦ ?_) ?_
    · change inner ℝ q (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤ 0
      rw [inner_normalVector_three_pi_div_two]
      rw [hKset] at hq
      linarith [(hxbox q hq).2.2.1]
    · have h := inner_le_supportValue K (hKset ▸ hpb) ((3 * Real.pi / 2 : ℝ) : Real.Angle)
      rwa [inner_normalVector_three_pi_div_two, hpb1, neg_zero] at h
  have hang : ((Real.pi / 2 + Real.pi : ℝ) : Real.Angle) =
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
    congr 1
    ring
  exact ⟨K, hKset, by positivity, le_rfl, hsvTop, hsvTop, by rw [hang]; exact hsvBot, hsvBot,
    C, hCnormals, hKset.trans hrep⟩

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Reflection
-/

public section

noncomputable section

namespace MovingSofa

/-- Exchange the two coordinates of the Euclidean plane. -/
@[expose]
def coordinateSwap : Point ≃ₗᵢ[ℝ] Point :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 1)

/-- Reflection exchanging the normals at angles zero and `ω + π / 2`. -/
def capReflection (ω : ℝ) : Point ≃ₗᵢ[ℝ] Point :=
  coordinateSwap.trans (EuclideanGeometry.o.rotation (ω : Real.Angle))

/-- First coordinate of the cap reflection. -/
theorem capReflection_apply_zero (ω : ℝ) (p : Point) :
    capReflection ω p 0 = -Real.sin ω * p 0 + Real.cos ω * p 1 := by
  rw [capReflection, LinearIsometryEquiv.trans_apply, Orientation.rotation_apply,
    rightAngleRotation_apply]
  simp [coordinateSwap]
  ring

/-- Second coordinate of the cap reflection. -/
theorem capReflection_apply_one (ω : ℝ) (p : Point) :
    capReflection ω p 1 = Real.cos ω * p 0 + Real.sin ω * p 1 := by
  rw [capReflection, LinearIsometryEquiv.trans_apply, Orientation.rotation_apply,
    rightAngleRotation_apply]
  simp [coordinateSwap]

/-- Reflection across the line through the upper vertex of the cap strip. -/
@[expose]
def stripTopReflection (ω : ℝ) (p : Point) : Point :=
  (2 * inner ℝ p (stripParallelogram ω).2.2 /
    inner ℝ (stripParallelogram ω).2.2 (stripParallelogram ω).2.2) •
      (stripParallelogram ω).2.2 - p

/-- The strip-top reflection is the explicit cap reflection. -/
theorem stripTopReflection_eq_capReflection (ω : ℝ)
    (hω0 : 0 < ω) (hωle : ω ≤ Real.pi / 2) :
    stripTopReflection ω = capReflection ω := by
  funext p
  by_cases hωtop : ω = Real.pi / 2
  · subst ω
    have harg : Real.pi / 4 - (Real.pi / 2) / 2 = 0 := by ring
    ext i
    fin_cases i
    · change stripTopReflection (Real.pi / 2) p 0 = capReflection (Real.pi / 2) p 0
      rw [capReflection_apply_zero]
      simp [stripTopReflection, stripParallelogram, harg, PiLp.inner_apply,
        Fin.sum_univ_two]
    · change stripTopReflection (Real.pi / 2) p 1 = capReflection (Real.pi / 2) p 1
      rw [capReflection_apply_one]
      have hnorm : ‖(!₂[0, 1] : Point)‖ ^ 2 = 1 := by
        simpa [Fin.sum_univ_two] using
          (EuclideanSpace.norm_sq_eq (!₂[0, 1] : Point))
      simp [stripTopReflection, stripParallelogram, harg, PiLp.inner_apply,
        Fin.sum_univ_two, hnorm]
      ring
  · have hωlt : ω < Real.pi / 2 := lt_of_le_of_ne hωle hωtop
    let C := Real.cos ω
    let S := Real.sin ω
    let c := Real.tan (Real.pi / 4 - ω / 2)
    have hC : 0 < C :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hω0], hωlt⟩
    have hgap : c = C⁻¹ - Real.tan ω := by
      simpa [c, show Real.pi / 4 - ω / 2 = (Real.pi / 2 - ω) / 2 by ring]
        using Real.tan_pi_div_two_sub_div_two ω ⟨hω0.le, hωlt⟩
    have htan : Real.tan ω = S / C := Real.tan_eq_sin_div_cos ω
    have hcC : c * C = 1 - S := by
      rw [hgap, htan]
      field_simp [hC.ne']
    have hc : c * (1 + S) = C := by
      rw [hgap, htan]
      field_simp [hC.ne']
      nlinarith [hcC, Real.sin_sq_add_cos_sq ω]
    have hcsq : c * c * (1 + S) = 1 - S := by
      calc
        c * c * (1 + S) = c * (c * (1 + S)) := by ring
        _ = c * C := by rw [hc]
        _ = 1 - S := hcC
    have hcoef₀ : c * c - 1 = -S * (c * c + 1) := by
      nlinarith [hcsq]
    have hbase : 2 = (1 + S) * (c * c + 1) := by
      nlinarith [hcoef₀]
    have hcoef₁ : 2 * c = C * (c * c + 1) := by
      rw [← hc]
      linear_combination c * hbase
    have hcoef₂ : 1 - c * c = S * (c * c + 1) := by
      nlinarith [hcsq]
    have hden : c * c + 1 ≠ 0 := by nlinarith [sq_nonneg c]
    ext i
    fin_cases i
    · change stripTopReflection ω p 0 = capReflection ω p 0
      rw [capReflection_apply_zero]
      simp only [stripTopReflection, stripParallelogram, PiLp.inner_apply,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Real.inner_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      simp only [mul_one]
      change 2 * (p 0 * c + p 1) / (c * c + 1) * c - p 0 =
        -S * p 0 + C * p 1
      field_simp [hden]
      linear_combination (p 0) * hcoef₀ + (p 1) * hcoef₁
    · change stripTopReflection ω p 1 = capReflection ω p 1
      rw [capReflection_apply_one]
      simp only [stripTopReflection, stripParallelogram, PiLp.inner_apply,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Real.inner_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      simp only [mul_one]
      change 2 * (p 0 * c + p 1) / (c * c + 1) - p 1 =
        C * p 0 + S * p 1
      field_simp [hden]
      linear_combination (p 0) * hcoef₁ + (p 1) * hcoef₂

/-- The strip-top reflection fixes the upper strip vertex. -/
theorem stripTopReflection_stripTop (ω : ℝ) :
    stripTopReflection ω (stripParallelogram ω).2.2 =
      (stripParallelogram ω).2.2 := by
  have ho : (stripParallelogram ω).2.2 ≠ (0 : Point) := by
    intro h
    have h1 := congrArg (fun p : Point ↦ p 1) h
    simp [stripParallelogram] at h1
  unfold stripTopReflection
  have hden : inner ℝ (stripParallelogram ω).2.2
      (stripParallelogram ω).2.2 ≠ 0 := inner_self_ne_zero.mpr ho
  rw [mul_div_assoc, div_self hden]
  module

/-- The cap reflection is an involution. -/
theorem capReflection_involutive (ω : ℝ) (p : Point) :
    capReflection ω (capReflection ω p) = p := by
  ext i
  fin_cases i
  · change capReflection ω (capReflection ω p) 0 = p 0
    rw [capReflection_apply_zero, capReflection_apply_zero, capReflection_apply_one]
    linear_combination (p 0) * (Real.sin_sq_add_cos_sq ω)
  · change capReflection ω (capReflection ω p) 1 = p 1
    rw [capReflection_apply_one, capReflection_apply_zero, capReflection_apply_one]
    linear_combination (p 1) * (Real.sin_sq_add_cos_sq ω)

/-- Reflection of a normal angle across the cap-reflection axis. -/
@[expose]
def reflectedAngle (ω : ℝ) (a : Real.Angle) : Real.Angle :=
  ((ω + Real.pi / 2 : ℝ) : Real.Angle) - a

/-- Reflection of normal angles is involutive. -/
theorem reflectedAngle_involutive (ω : ℝ) (a : Real.Angle) :
    reflectedAngle ω (reflectedAngle ω a) = a := by
  simp only [reflectedAngle]
  abel

/-- Coercion formula for a reflected real angle. -/
theorem reflectedAngle_coe (ω t : ℝ) :
    reflectedAngle ω (t : Real.Angle) =
      ((ω + Real.pi / 2 - t : ℝ) : Real.Angle) := by
  simp only [reflectedAngle, Real.Angle.coe_sub, Real.Angle.coe_add]

/-- The cap reflection transports normal vectors at real angles. -/
theorem capReflection_normalVector (ω a : ℝ) :
    capReflection ω (normalVector (a : Real.Angle)) =
      normalVector ((ω + Real.pi / 2 - a : ℝ) : Real.Angle) := by
  have hrho : (ω : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) -
      (a : Real.Angle) = ((ω + Real.pi / 2 - a : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_add, ← Real.Angle.coe_sub]
  ext i
  fin_cases i
  · change capReflection ω (normalVector (a : Real.Angle)) 0 =
      normalVector ((ω + Real.pi / 2 - a : ℝ) : Real.Angle) 0
    rw [capReflection_apply_zero, ← hrho]
    simp only [Fin.isValue, normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Matrix.cons_val_zero, neg_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [hrho, Real.Angle.cos_coe, Real.cos_sub, Real.sin_add, Real.cos_add]
    simp
  · change capReflection ω (normalVector (a : Real.Angle)) 1 =
      normalVector ((ω + Real.pi / 2 - a : ℝ) : Real.Angle) 1
    rw [capReflection_apply_one, ← hrho]
    simp only [Fin.isValue, normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [hrho, Real.Angle.sin_coe, Real.sin_sub, Real.sin_add, Real.cos_add]
    simp

/-- The cap reflection reverses tangent vectors at real angles. -/
theorem capReflection_tangentVector (ω a : ℝ) :
    capReflection ω (tangentVector (a : Real.Angle)) =
      -tangentVector ((ω + Real.pi / 2 - a : ℝ) : Real.Angle) := by
  have hrho : (ω : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) -
      (a : Real.Angle) = ((ω + Real.pi / 2 - a : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_add, ← Real.Angle.coe_sub]
  ext i
  fin_cases i
  · change capReflection ω (tangentVector (a : Real.Angle)) 0 =
      (-tangentVector ((ω + Real.pi / 2 - a : ℝ) : Real.Angle)) 0
    rw [capReflection_apply_zero, ← hrho]
    simp only [Fin.isValue, tangentVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Matrix.cons_val_zero, mul_neg, neg_mul, neg_neg, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, PiLp.neg_apply]
    rw [hrho, Real.Angle.sin_coe, Real.sin_sub, Real.sin_add, Real.cos_add]
    simp
    ring
  · change capReflection ω (tangentVector (a : Real.Angle)) 1 =
      (-tangentVector ((ω + Real.pi / 2 - a : ℝ) : Real.Angle)) 1
    rw [capReflection_apply_one, ← hrho]
    simp only [Fin.isValue, tangentVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Matrix.cons_val_zero, mul_neg, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      PiLp.neg_apply]
    rw [hrho, Real.Angle.cos_coe, Real.cos_sub, Real.sin_add, Real.cos_add]
    simp

/-- The cap reflection transports normal vectors by reflected angles. -/
theorem capReflection_normalVector_angle (ω : ℝ) (a : Real.Angle) :
    capReflection ω (normalVector a) = normalVector (reflectedAngle ω a) := by
  calc
    capReflection ω (normalVector a) =
        capReflection ω (normalVector (a.toReal : Real.Angle)) := by rw [a.coe_toReal]
    _ = normalVector ((ω + Real.pi / 2 - a.toReal : ℝ) : Real.Angle) :=
      capReflection_normalVector ω a.toReal
    _ = normalVector (reflectedAngle ω a) := by
      congr 1
      simp only [reflectedAngle, Real.Angle.coe_sub, Real.Angle.coe_add, a.coe_toReal]

/-- The cap reflection reverses tangent vectors at reflected angles. -/
theorem capReflection_tangentVector_angle (ω : ℝ) (a : Real.Angle) :
    capReflection ω (tangentVector a) = -tangentVector (reflectedAngle ω a) := by
  calc
    capReflection ω (tangentVector a) =
        capReflection ω (tangentVector (a.toReal : Real.Angle)) := by rw [a.coe_toReal]
    _ = -tangentVector ((ω + Real.pi / 2 - a.toReal : ℝ) : Real.Angle) :=
      capReflection_tangentVector ω a.toReal
    _ = -tangentVector (reflectedAngle ω a) := by
      congr 2
      simp only [reflectedAngle, Real.Angle.coe_sub, Real.Angle.coe_add, a.coe_toReal]

/-- Inner products with normals transform under the cap reflection. -/
theorem inner_capReflection_normalVector (ω : ℝ) (p : Point)
    (a : Real.Angle) :
    inner ℝ (capReflection ω p) (normalVector a) =
      inner ℝ p (normalVector (reflectedAngle ω a)) := by
  have hn : capReflection ω (normalVector (reflectedAngle ω a)) =
      normalVector a := by
    rw [capReflection_normalVector_angle, reflectedAngle_involutive]
  rw [← hn]
  exact (capReflection ω).inner_map_map p (normalVector (reflectedAngle ω a))

/-- Inner products with tangents transform under the cap reflection. -/
theorem inner_capReflection_tangentVector (ω : ℝ) (p : Point)
    (a : Real.Angle) :
    inner ℝ (capReflection ω p) (tangentVector a) =
      -inner ℝ p (tangentVector (reflectedAngle ω a)) := by
  have ht : capReflection ω (-tangentVector (reflectedAngle ω a)) =
      tangentVector a := by
    rw [map_neg, capReflection_tangentVector_angle, reflectedAngle_involutive,
      neg_neg]
  rw [← ht, (capReflection ω).inner_map_map, inner_neg_right]

/-- The cap reflection transports every open or closed normal half-plane. -/
theorem capReflection_image_normalHalfPlane (ω h : ℝ)
    (a : Real.Angle) (upper strict : Bool) :
    capReflection ω '' normalHalfPlane a h upper strict =
      normalHalfPlane (reflectedAngle ω a) h upper strict := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    cases upper <;> cases strict <;>
      simp only [normalHalfPlane, Bool.false_eq_true, ↓reduceIte,
        Set.mem_ofPred_eq] at hq ⊢ <;>
      rwa [inner_capReflection_normalVector, reflectedAngle_involutive]
  · intro hp
    refine ⟨capReflection ω p, ?_, capReflection_involutive ω p⟩
    cases upper <;> cases strict <;>
      simp only [normalHalfPlane, Bool.false_eq_true, ↓reduceIte,
        Set.mem_ofPred_eq] at hp ⊢ <;>
      rwa [inner_capReflection_normalVector]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Supporting Hallway
-/

public section

noncomputable section

namespace MovingSofa

private theorem supportValue_le_of_subset_rotatedHallway (s : Set Point) (t : Real.Angle)
    (hs : s.Nonempty) (v : Point)
    (hv : s ⊆ (fun p ↦ rotationMap t p + v) '' hallway) :
    supportValue s t ≤ 1 + inner ℝ v (normalVector t) ∧
      supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) ≤
        1 + inner ℝ v (tangentVector t) := by
  have hbound₁ : supportValue s t ≤ 1 + inner ℝ v (normalVector t) := by
    apply csSup_le (hs.image _)
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨q, hq, rfl⟩ := hv hp
    dsimp only
    rw [inner_add_left, inner_rotationMap_normalVector]
    linarith [(mem_hallway_iff q).mp hq |>.1.1]
  have hbound₂ : supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) ≤
      1 + inner ℝ v (tangentVector t) := by
    apply csSup_le (hs.image _)
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨q, hq, rfl⟩ := hv hp
    dsimp only
    rw [normalVector_add_pi_div_two, inner_add_left, inner_rotationMap_tangentVector]
    linarith [(mem_hallway_iff q).mp hq |>.1.2]
  exact ⟨hbound₁, hbound₂⟩

theorem subset_supportingHallway (s : Set Point) (t : Real.Angle)
    (hs : s.Nonempty) (hc : IsCompact s)
    (hL : ∃ v : Point, s ⊆ (fun p ↦ rotationMap t p + v) '' hallway) :
    s ⊆ supportingHallway s t := by
  rcases hL with ⟨v, hv⟩
  obtain ⟨hbound₁, hbound₂⟩ := supportValue_le_of_subset_rotatedHallway s t hs v hv
  intro p hp
  obtain ⟨x, hx⟩ := (EuclideanGeometry.o.rotation t).surjective
    (p - (supportValue s t - 1) • normalVector t -
      (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) • tangentVector t)
  have hxp : supportingPlacement s t x = p := by
    simp only [supportingPlacement, rotationMap, hx]
    abel
  have hx₀ := inner_supportingPlacement_normalVector s t x
  have hx₁ := inner_supportingPlacement_tangentVector s t x
  rw [hxp] at hx₀ hx₁
  have hsup (w : Real.Angle) : inner ℝ p (normalVector w) ≤ supportValue s w :=
    le_csSup (hc.bddAbove_image (continuous_id.inner continuous_const).continuousOn)
      ⟨p, hp, rfl⟩
  have hupper₀ := hsup t
  have hupper₁ := hsup (t + ((Real.pi / 2 : ℝ) : Real.Angle))
  rw [normalVector_add_pi_div_two] at hupper₁
  refine ⟨x, (mem_hallway_iff x).mpr ⟨⟨by linarith, by linarith⟩, ?_⟩, hxp⟩
  obtain ⟨q, hq, hqp⟩ := hv hp
  rcases (mem_hallway_iff q).mp hq |>.2 with hq₀ | hq₁
  · have hcoord : inner ℝ p (normalVector t) = q 0 + inner ℝ v (normalVector t) := by
      rw [← hqp, inner_add_left, inner_rotationMap_normalVector]
    exact Or.inl (by linarith)
  · have hcoord : inner ℝ p (tangentVector t) = q 1 + inner ℝ v (tangentVector t) := by
      rw [← hqp, inner_add_left, inner_rotationMap_tangentVector]
    exact Or.inr (by linarith)

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Analysis.SurfaceMeasure.UpperGraph`.
* `Analysis.SurfaceMeasure.ExposedFrontier`.
* `Analysis.SurfaceMeasure.RegularBoundaryHelpers`.
* `Analysis.SurfaceMeasure.GraphIntegral`.
* `Analysis.SurfaceMeasure.Construction`.
* `Analysis.SurfaceMeasure.GraphConvergence`.
* `Analysis.SurfaceMeasure.Properties`.
* `Analysis.SurfaceMeasure.BoundaryExtension`.
* `Analysis.SurfaceMeasure.Opposite`.
* `Analysis.SurfaceMeasure.WeakConvergence`.
* `Analysis.SurfaceMeasure.AtomLimits`.
* `Analysis.SurfaceMeasure.WeightedBoundary`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Upper Graph
-/

public section

noncomputable section

open MeasureTheory
open scoped Pointwise

namespace MovingSofa

private def negCoordinates (e : Point ≃ₗᵢ[ℝ] Point) : Point ≃ₗᵢ[ℝ] Point :=
  e.trans (LinearIsometryEquiv.neg ℝ)

private def swapCoordinates (e : Point ≃ₗᵢ[ℝ] Point) : Point ≃ₗᵢ[ℝ] Point :=
  e.trans coordinateSwap

@[simp] private theorem negCoordinates_apply (e : Point ≃ₗᵢ[ℝ] Point) (p : Point) (i : Fin 2) :
    negCoordinates e p i = -e p i := by
  simp [negCoordinates]

@[simp] private theorem swapCoordinates_apply_zero (e : Point ≃ₗᵢ[ℝ] Point)
    (p : Point) : swapCoordinates e p 0 = e p 1 := by
  simp [swapCoordinates, coordinateSwap]

@[simp] private theorem swapCoordinates_apply_one (e : Point ≃ₗᵢ[ℝ] Point)
    (p : Point) : swapCoordinates e p 1 = e p 0 := by
  simp [swapCoordinates, coordinateSwap]

/-- The upper graph height is the greatest vertical coordinate in its fiber. -/
theorem upperGraphHeight_isGreatest (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {x : ℝ} (hx : x ∈ horizontalProjection K o e) :
    IsGreatest {y : ℝ | o + e.symm !₂[x, y] ∈ (K : Set Point)}
      (upperGraphHeight K o e x) := by
  let F : Set ℝ := {y | o + e.symm !₂[x, y] ∈ (K : Set Point)}
  let Y : Set ℝ := (fun p : Point ↦ e (p - o) 1) '' (K : Set Point)
  have hY : IsCompact Y := K.isCompact.image (by fun_prop)
  have hFc : IsClosed F := K.isClosed.preimage (by fun_prop)
  have hFY : F ⊆ Y := by
    intro y hy
    refine ⟨o + e.symm !₂[x, y], hy, ?_⟩
    simp
  have hF : IsCompact F := hY.of_isClosed_subset hFc hFY
  have hFne : F.Nonempty := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨e (p - o) 1, ?_⟩
    dsimp [F]
    convert hp using 1
    apply sub_eq_zero.mp
    apply e.injective
    ext i
    fin_cases i
    · simp only [map_sub, PiLp.sub_apply] at hpx
      simp
      linarith
    · simp
  change IsGreatest F (sSup F)
  exact hF.isGreatest_sSup hFne

/-- An attained upper graph point belongs to the convex body. -/
theorem upperGraphHeight_mem (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {x : ℝ} (hx : x ∈ horizontalProjection K o e) :
    o + e.symm !₂[x, upperGraphHeight K o e x] ∈ (K : Set Point) :=
  (upperGraphHeight_isGreatest K o e hx).1

private theorem upperGraphHeight_eq_coordinate_of_isExteriorNormal_of_pos
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {p : Point} (hp : p ∈ K)
    {a : Real.Angle} (ha : IsExteriorNormal K p a) (hpos : 0 < e (normalVector a) 1) :
    upperGraphHeight K o e (e (p - o) 0) = e (p - o) 1 := by
  have hx : e (p - o) 0 ∈ horizontalProjection K o e := ⟨p, hp, rfl⟩
  apply le_antisymm
  · apply le_of_not_gt
    intro hgt
    have hmem := upperGraphHeight_mem K o e hx
    have hs := ha (o + e.symm !₂[e (p - o) 0,
      upperGraphHeight K o e (e (p - o) 0)]) hmem
    rw [← e.inner_map_map] at hs
    simp only [map_sub, map_add, LinearIsometryEquiv.apply_symm_apply, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, PiLp.sub_apply, PiLp.add_apply] at hs
    have hzero : e (p - o) 0 = e p 0 - e o 0 := by simp
    have hone : e (p - o) 1 = e p 1 - e o 1 := by simp
    ring_nf at hs
    rw [hzero, hone] at hgt
    rw [show -(e o 0) + e p 0 = e p 0 - e o 0 by ring] at hs
    have hnonpos : e (normalVector a) 1 *
        (upperGraphHeight K o e (e p 0 - e o 0) - (e p 1 - e o 1)) ≤ 0 := by
      nlinarith [hs]
    exact (not_lt_of_ge hnonpos) (mul_pos hpos (sub_pos.mpr hgt))
  · exact (upperGraphHeight_isGreatest K o e hx).2 (by
      change o + e.symm !₂[e (p - o) 0, e (p - o) 1] ∈ (K : Set Point)
      rw [show o + e.symm !₂[e (p - o) 0, e (p - o) 1] = p by
        apply e.injective
        ext i
        fin_cases i <;> simp [map_sub]]
      exact hp)

/-- A boundary point whose exterior normal has positive vertical coordinate lies
on the upper coordinate graph. -/
theorem eq_upperCoordinateGraph_of_isExteriorNormal_of_pos
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {p : Point} (hp : p ∈ K)
    {a : Real.Angle} (ha : IsExteriorNormal K p a) (hpos : 0 < e (normalVector a) 1) :
    p = o + e.symm !₂[e (p - o) 0, upperGraphHeight K o e (e (p - o) 0)] := by
  rw [upperGraphHeight_eq_coordinate_of_isExteriorNormal_of_pos K o e hp ha hpos]
  apply e.injective
  ext i
  fin_cases i <;> simp [map_sub]

private theorem eq_upperCoordinateGraph_of_maximal_verticalCoordinate
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {p : Point} (hp : p ∈ K)
    (hmax : ∀ q ∈ K, e (q - o) 1 ≤ e (p - o) 1) :
    p = o + e.symm !₂[e (p - o) 0, upperGraphHeight K o e (e (p - o) 0)] := by
  have hx : e (p - o) 0 ∈ horizontalProjection K o e := ⟨p, hp, rfl⟩
  have hpGreatest : IsGreatest
      {y : ℝ | o + e.symm !₂[e (p - o) 0, y] ∈ (K : Set Point)} (e (p - o) 1) := by
    constructor
    · change o + e.symm !₂[e (p - o) 0, e (p - o) 1] ∈ (K : Set Point)
      rw [show o + e.symm !₂[e (p - o) 0, e (p - o) 1] = p by
        apply e.injective
        ext i
        fin_cases i <;> simp [map_sub]]
      exact hp
    · intro y hy
      have := hmax (o + e.symm !₂[e (p - o) 0, y]) hy
      simpa using this
  have heq := (upperGraphHeight_isGreatest K o e hx).unique hpGreatest
  rw [heq]
  apply e.injective
  ext i
  fin_cases i <;> simp [map_sub]

private theorem horizontalCoordinate_le_rightBound (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {p : Point} (hp : p ∈ K) :
    e (p - o) 0 ≤ (horizontalBounds K o e).2 := by
  exact (K.isCompact.image (by fun_prop)).isGreatest_sSup (K.nonempty.image _)
    |>.2 ⟨p, hp, rfl⟩

private theorem horizontalProjection_negCoordinates (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) :
    horizontalProjection K o (negCoordinates e) = -(horizontalProjection K o e) := by
  ext x
  simp only [horizontalProjection, negCoordinates, LinearIsometryEquiv.trans_apply, map_sub,
    LinearIsometryEquiv.coe_neg, Fin.isValue, PiLp.sub_apply, PiLp.neg_apply, Set.mem_image,
    SetLike.mem_coe, Set.mem_neg]
  constructor
  · rintro ⟨p, hp, h⟩
    exact ⟨p, hp, by linarith⟩
  · rintro ⟨p, hp, h⟩
    exact ⟨p, hp, by linarith⟩

private theorem horizontalBounds_negCoordinates (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) :
    horizontalBounds K o (negCoordinates e) =
      (-(horizontalBounds K o e).2, -(horizontalBounds K o e).1) := by
  simp only [horizontalBounds, horizontalProjection_negCoordinates, Real.sInf_neg,
    Real.sSup_neg]

private theorem leftBound_le_horizontalCoordinate (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {p : Point} (hp : p ∈ K) :
    (horizontalBounds K o e).1 ≤ e (p - o) 0 := by
  exact (K.isCompact.image (by fun_prop)).isLeast_sInf (K.nonempty.image _)
    |>.2 ⟨p, hp, rfl⟩

private theorem eq_swapUpperGraph_of_horizontalCoordinate_eq_rightBound
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {p : Point} (hp : p ∈ K)
    (hpr : e (p - o) 0 = (horizontalBounds K o e).2) :
    p = o + (swapCoordinates e).symm
      !₂[swapCoordinates e (p - o) 0,
        upperGraphHeight K o (swapCoordinates e) (swapCoordinates e (p - o) 0)] := by
  apply eq_upperCoordinateGraph_of_maximal_verticalCoordinate K o (swapCoordinates e) hp
  intro q hq
  have hqle := horizontalCoordinate_le_rightBound K o e hq
  simp only [swapCoordinates_apply_one]
  simp only [map_sub, PiLp.sub_apply] at hpr hqle ⊢
  linarith

private theorem eq_negSwapUpperGraph_of_horizontalCoordinate_eq_leftBound
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {p : Point} (hp : p ∈ K)
    (hpl : e (p - o) 0 = (horizontalBounds K o e).1) :
    p = o + (negCoordinates (swapCoordinates e)).symm
      !₂[negCoordinates (swapCoordinates e) (p - o) 0,
        upperGraphHeight K o (negCoordinates (swapCoordinates e))
          (negCoordinates (swapCoordinates e) (p - o) 0)] := by
  apply eq_upperCoordinateGraph_of_maximal_verticalCoordinate K o
    (negCoordinates (swapCoordinates e)) hp
  intro q hq
  have hle := leftBound_le_horizontalCoordinate K o e hq
  simp only [negCoordinates_apply, swapCoordinates_apply_one]
  simp only [map_sub, PiLp.sub_apply] at hpl hle ⊢
  linarith

private def coordinateCornerSet (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) : Set Point :=
  {p | e (p - o) 0 ∈ ({(horizontalBounds K o e).1,
      (horizontalBounds K o e).2} : Set ℝ) ∧
    e (p - o) 1 ∈ ({(horizontalBounds K o (swapCoordinates e)).1,
      (horizontalBounds K o (swapCoordinates e)).2} : Set ℝ)}

private theorem coordinateCornerSet_finite (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) : (coordinateCornerSet K o e).Finite := by
  let coords : Point → ℝ × ℝ := fun p ↦ (e (p - o) 0, e (p - o) 1)
  let xs : Set ℝ := {(horizontalBounds K o e).1, (horizontalBounds K o e).2}
  let ys : Set ℝ := {(horizontalBounds K o (swapCoordinates e)).1,
    (horizontalBounds K o (swapCoordinates e)).2}
  have hcoords : Function.Injective coords := by
    intro p q hpq
    apply sub_left_injective (b := o)
    apply e.injective
    ext i
    fin_cases i
    · exact congrArg Prod.fst hpq
    · exact congrArg Prod.snd hpq
  have hfinite : (xs ×ˢ ys).Finite := Set.toFinite xs |>.prod (Set.toFinite ys)
  have hpre : (coords ⁻¹' (xs ×ˢ ys)).Finite := hfinite.preimage hcoords.injOn
  have heq : coordinateCornerSet K o e = coords ⁻¹' (xs ×ˢ ys) := by
    ext p
    simp only [coordinateCornerSet, coords, xs, ys, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_prod, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [heq]
  exact hpre

private theorem hausdorffMeasure_coordinateCornerSet_eq_zero (K : ConvexBody Point)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) :
    Measure.hausdorffMeasure 1 (coordinateCornerSet K o e) = 0 := by
  let _ := MeasureTheory.Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  exact (coordinateCornerSet_finite K o e).measure_zero _

/-- The upper height function of a convex body is concave on its projection. -/
theorem concaveOn_upperGraphHeight (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) :
    ConcaveOn ℝ (horizontalProjection K o e) (upperGraphHeight K o e) := by
  have hproj : Convex ℝ (horizontalProjection K o e) := by
    intro x hx y hy a b ha hb hab
    obtain ⟨p, hp, hpx⟩ := hx
    obtain ⟨q, hq, hqx⟩ := hy
    refine ⟨a • p + b • q, K.convex hp hq ha hb hab, ?_⟩
    simp only [map_sub, map_add, map_smul, PiLp.sub_apply, PiLp.add_apply,
      PiLp.smul_apply] at hpx hqx ⊢
    linear_combination a * hpx + b * hqx + e o 0 * hab
  refine ⟨hproj, ?_⟩
  · intro x hx y hy a b ha hb hab
    apply (upperGraphHeight_isGreatest K o e (by
      exact hproj hx hy ha hb hab)).2
    have hpx := upperGraphHeight_mem K o e hx
    have hpy := upperGraphHeight_mem K o e hy
    have hconv := K.convex hpx hpy ha hb hab
    change o + e.symm !₂[a • x + b • y,
      a • upperGraphHeight K o e x + b • upperGraphHeight K o e y] ∈ (K : Set Point)
    rw [show o + e.symm !₂[a • x + b • y,
        a • upperGraphHeight K o e x + b • upperGraphHeight K o e y] =
        a • (o + e.symm !₂[x, upperGraphHeight K o e x]) +
          b • (o + e.symm !₂[y, upperGraphHeight K o e y]) by
      apply e.injective
      ext i
      fin_cases i <;> simp [map_add, map_smul] <;>
        linear_combination -(e o _) * hab]
    exact hconv

/-- The horizontal projection is the interval between its compact extrema. -/
theorem horizontalProjection_eq_Icc (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) :
    horizontalProjection K o e =
      Set.Icc (horizontalBounds K o e).1 (horizontalBounds K o e).2 := by
  let s := horizontalProjection K o e
  have hscompact : IsCompact s := K.isCompact.image (by fun_prop)
  have hsne : s.Nonempty := K.nonempty.image _
  have hsconv : Convex ℝ s := (concaveOn_upperGraphHeight K o e).1
  change s = Set.Icc (sInf s) (sSup s)
  apply Set.Subset.antisymm
  · exact hscompact.isBounded.subset_Icc_sInf_sSup
  · have hle := (hscompact.isLeast_sInf hsne).2 (hscompact.sSup_mem hsne)
    rw [← Set.uIcc_of_le hle, ← segment_eq_uIcc]
    exact hsconv.segment_subset (hscompact.sInf_mem hsne) (hscompact.sSup_mem hsne)

/-- The upper boundary height is locally Lipschitz inside its projection interval. -/
theorem locallyLipschitzOn_upperGraphHeight (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) :
    LocallyLipschitzOn
      (Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2)
      (upperGraphHeight K o e) := by
  have hlip := (concaveOn_upperGraphHeight K o e).locallyLipschitzOn_interior
  rw [horizontalProjection_eq_Icc K o e, interior_Icc] at hlip
  exact hlip

/-- The upward normal determined by the derivative of an upper graph is exterior. -/
theorem upperGraph_deriv_isExteriorNormal (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {x : ℝ}
    (hx : x ∈ Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2)
    (hdiff : DifferentiableAt ℝ (upperGraphHeight K o e) x) :
    IsExteriorNormal K (o + e.symm !₂[x, upperGraphHeight K o e x])
      (vectorNormalAngle (e.symm !₂[-deriv (upperGraphHeight K o e) x, 1])) := by
  let g := upperGraphHeight K o e
  let q : Point := e.symm !₂[-deriv g x, 1]
  have hq : q ≠ 0 := by
    intro hzero
    have := congrFun (congrArg WithLp.ofLp (congrArg e hzero)) 1
    simp [q] at this
  change IsExteriorNormal K (o + e.symm !₂[x, g x]) (vectorNormalAngle q)
  rw [IsExteriorNormal]
  rw [normalVector_vectorNormalAngle hq]
  intro p hp
  have hxp : e (p - o) 0 ∈ horizontalProjection K o e := ⟨p, hp, rfl⟩
  have hxproj : x ∈ horizontalProjection K o e := by
    rw [horizontalProjection_eq_Icc K o e]
    exact ⟨hx.1.le, hx.2.le⟩
  have hvertical : e (p - o) 1 ≤ g (e (p - o) 0) :=
    (upperGraphHeight_isGreatest K o e hxp).2 (by
      change o + e.symm !₂[e (p - o) 0, e (p - o) 1] ∈ (K : Set Point)
      rw [show o + e.symm !₂[e (p - o) 0, e (p - o) 1] = p by
        apply e.injective
        ext i
        fin_cases i <;> simp [map_sub]]
      exact hp)
  have htangent := ConcaveOn.le_add_deriv_mul_sub
    (concaveOn_upperGraphHeight K o e) hxproj hdiff hxp
  have hvertical' : e p 1 - e o 1 ≤ g (e p 0 - e o 0) := by
    simpa only [map_sub, PiLp.sub_apply] using hvertical
  have htangent' : g (e p 0 - e o 0) ≤
      g x + deriv g x * ((e p 0 - e o 0) - x) := by
    simpa only [map_sub, PiLp.sub_apply] using htangent
  rw [inner_smul_right]
  apply mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg q))
  rw [← e.inner_map_map]
  simp only [map_sub, map_add, LinearIsometryEquiv.apply_symm_apply, q, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, PiLp.sub_apply, PiLp.add_apply]
  dsimp only [g] at hvertical' htangent' ⊢
  nlinarith [hvertical', htangent']

/-- Angular normal vectors have norm one. -/
theorem norm_normalVector (a : Real.Angle) : ‖normalVector a‖ = 1 := by
  induction a using Real.Angle.induction_on with
  | _ a =>
    rw [EuclideanSpace.norm_eq]
    simp [normalVector, frame, Fin.sum_univ_two]

private theorem horizontalCoordinate_eq_endpoint_of_isExteriorNormal_of_vertical_eq_zero
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {p : Point} (hp : p ∈ K)
    {a : Real.Angle} (ha : IsExteriorNormal K p a)
    (hzero : e (normalVector a) 1 = 0) :
    e (p - o) 0 = (horizontalBounds K o e).1 ∨
      e (p - o) 0 = (horizontalBounds K o e).2 := by
  have hxne : e (normalVector a) 0 ≠ 0 := by
    intro hx
    have he : e (normalVector a) = 0 := by
      ext i
      fin_cases i <;> simp [hx, hzero]
    have hn : ‖e (normalVector a)‖ = 1 := by rw [e.norm_map, norm_normalVector]
    simp [he] at hn
  rcases lt_or_gt_of_ne hxne with hneg | hpos
  · left
    have hleast : IsLeast (horizontalProjection K o e) (e (p - o) 0) := by
      refine ⟨⟨p, hp, rfl⟩, ?_⟩
      rintro x ⟨q, hq, rfl⟩
      have hs := ha q hq
      rw [← e.inner_map_map] at hs
      simp only [map_sub, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
        Fin.sum_univ_two, PiLp.sub_apply, hzero] at hs
      have hxcoord : e (q - o) 0 - e (p - o) 0 = e q 0 - e p 0 := by simp
      nlinarith
    exact hleast.unique ((K.isCompact.image (by fun_prop)).isLeast_sInf (K.nonempty.image _))
  · right
    have hgreatest : IsGreatest (horizontalProjection K o e) (e (p - o) 0) := by
      refine ⟨⟨p, hp, rfl⟩, ?_⟩
      rintro x ⟨q, hq, rfl⟩
      have hs := ha q hq
      rw [← e.inner_map_map] at hs
      simp only [map_sub, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
        Fin.sum_univ_two, PiLp.sub_apply, hzero] at hs
      have hxcoord : e (q - o) 0 - e (p - o) 0 = e q 0 - e p 0 := by simp
      nlinarith
    exact hgreatest.unique ((K.isCompact.image (by fun_prop)).isGreatest_sSup
      (K.nonempty.image _))

/-- A point of a convex body admitting an exterior unit normal belongs to its frontier. -/
theorem mem_frontier_of_mem_of_isExteriorNormal (K : ConvexBody Point)
    {p : Point} (hp : p ∈ K) {a : Real.Angle} (ha : IsExteriorNormal K p a) :
    p ∈ frontier (K : Set Point) := by
  rw [mem_frontier_iff_notMem_interior hp]
  intro hpint
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hpint
  let q := p + (ε / 2) • normalVector a
  have hqp : q ∈ K := interior_subset (hball (by
    rw [Metric.mem_ball, dist_eq_norm]
    rw [show q - p = (ε / 2) • normalVector a by simp [q], norm_smul,
      norm_normalVector]
    rw [Real.norm_eq_abs, abs_of_pos (div_pos hε (by norm_num))]
    linarith))
  have := ha q hqp
  rw [show q - p = (ε / 2) • normalVector a by simp [q], inner_smul_left,
    real_inner_self_eq_norm_sq, norm_normalVector a] at this
  have hnonpos : ε / 2 ≤ 0 := by simpa using this
  linarith

private theorem upperGraph_tangent_orthogonal_of_isExteriorNormal
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {x : ℝ}
    (hx : x ∈ Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2)
    (hdiff : DifferentiableAt ℝ (upperGraphHeight K o e) x) {a : Real.Angle}
    (ha : IsExteriorNormal K
      (o + e.symm !₂[x, upperGraphHeight K o e x]) a) :
    inner ℝ (e.symm !₂[1, deriv (upperGraphHeight K o e) x]) (normalVector a) = 0 := by
  let g := upperGraphHeight K o e
  let n := e (normalVector a)
  let f : ℝ → ℝ := fun y ↦ (y - x) * n 0 + (g y - g x) * n 1
  have hlocal : IsLocalMax f x := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    have hyproj : y ∈ horizontalProjection K o e := by
      rw [horizontalProjection_eq_Icc K o e]
      exact ⟨hy.1.le, hy.2.le⟩
    have hmem := upperGraphHeight_mem K o e hyproj
    have hsupport := ha (o + e.symm !₂[y, g y]) hmem
    rw [← e.inner_map_map] at hsupport
    simp only [map_sub, map_add, LinearIsometryEquiv.apply_symm_apply, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, PiLp.sub_apply, PiLp.add_apply] at hsupport
    dsimp only [f, g, n]
    dsimp only [g] at hsupport
    nlinarith [hsupport]
  have hfderiv : HasDerivAt f (n 0 + deriv g x * n 1) x := by
    convert (((hasDerivAt_id x).sub_const x).mul_const (n 0)).add
      ((hdiff.hasDerivAt.sub_const (g x)).mul_const (n 1)) using 1
    · funext y
      rfl
    · simp [g]
  have hzero := hlocal.hasDerivAt_eq_zero hfderiv
  rw [← e.inner_map_map]
  simp only [LinearIsometryEquiv.apply_symm_apply, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  dsimp only [g, n] at hzero ⊢
  nlinarith [hzero]

private theorem normalVector_injective : Function.Injective normalVector := by
  intro a b hab
  induction a using Real.Angle.induction_on with
  | _ a =>
    induction b using Real.Angle.induction_on with
    | _ b =>
      apply Real.Angle.cos_sin_inj
      · exact congrFun (congrArg WithLp.ofLp hab) 0
      · exact congrFun (congrArg WithLp.ofLp hab) 1

private theorem exteriorNormal_eq_of_orthogonal_of_interior_nonempty
    (K : ConvexBody Point) (hK : (interior (K : Set Point)).Nonempty)
    {p v : Point} (hv : v ≠ 0) {a b : Real.Angle}
    (ha : IsExteriorNormal K p a) (hb : IsExteriorNormal K p b)
    (hva : inner ℝ v (normalVector a) = 0)
    (hvb : inner ℝ v (normalVector b) = 0) : a = b := by
  let orientation : Orientation ℝ Point (Fin 2) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  rcases EuclideanGeometry.eq_or_eq_neg_of_unit_orthogonal orientation hv (norm_normalVector a)
      (norm_normalVector b) hva hvb with hab | hab
  · exact normalVector_injective hab
  · exfalso
    obtain ⟨z, hz⟩ := hK
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
    let q := z + (ε / 2) • normalVector a
    have hq : q ∈ K := interior_subset (hball (by
      rw [Metric.mem_ball, dist_eq_norm]
      rw [show q - z = (ε / 2) • normalVector a by simp [q], norm_smul,
        norm_normalVector, Real.norm_eq_abs, abs_of_pos (div_pos hε (by norm_num))]
      norm_num
      linarith))
    have haz := ha z (interior_subset hz)
    have hbz := hb z (interior_subset hz)
    have hba : normalVector b = -normalVector a := by rw [hab]; simp
    rw [hba, inner_neg_right] at hbz
    have heq : inner ℝ (z - p) (normalVector a) = 0 := by linarith
    have haq := ha q hq
    have hqp : q - p = (z - p) + (ε / 2) • normalVector a := by
      dsimp only [q]
      module
    rw [hqp,
      inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq,
      norm_normalVector a, heq, zero_add] at haq
    have : ε / 2 ≤ 0 := by simpa using haq
    linarith

/-- A differentiable interior point of an upper boundary graph is regular. -/
theorem upperGraph_mem_regularBoundary (K : ConvexBody Point)
    (hK : (interior (K : Set Point)).Nonempty) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    {x : ℝ} (hx : x ∈ Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2)
    (hdiff : DifferentiableAt ℝ (upperGraphHeight K o e) x) :
    o + e.symm !₂[x, upperGraphHeight K o e x] ∈ regularBoundary K := by
  let p := o + e.symm !₂[x, upperGraphHeight K o e x]
  let a := vectorNormalAngle
    (e.symm !₂[-deriv (upperGraphHeight K o e) x, 1])
  have hxproj : x ∈ horizontalProjection K o e := by
    rw [horizontalProjection_eq_Icc K o e]
    exact ⟨hx.1.le, hx.2.le⟩
  have hp : p ∈ K := upperGraphHeight_mem K o e hxproj
  have ha : IsExteriorNormal K p a := upperGraph_deriv_isExteriorNormal K o e hx hdiff
  refine ⟨mem_frontier_of_mem_of_isExteriorNormal K hp ha, a, ha, ?_⟩
  intro b hb
  symm
  apply exteriorNormal_eq_of_orthogonal_of_interior_nonempty K hK
    (v := e.symm !₂[1, deriv (upperGraphHeight K o e) x])
  · intro hv
    have := congrFun (congrArg WithLp.ofLp (congrArg e hv)) 0
    simp at this
  · exact ha
  · exact hb
  · rw [normalVector_vectorNormalAngle]
    · rw [← e.inner_map_map]
      simp [PiLp.inner_apply, Fin.sum_univ_two]
    · intro hv
      have := congrFun (congrArg WithLp.ofLp (congrArg e hv)) 1
      simp at this
  · exact upperGraph_tangent_orthogonal_of_isExteriorNormal K o e hx hdiff (a := b) hb

/-- Points of an upper graph lying above nondifferentiability parameters. -/
def irregularUpperGraph (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) : Set Point :=
  (fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x]) ''
    {x | x ∈ Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2 ∧
      ¬ DifferentiableAt ℝ (upperGraphHeight K o e) x}

/-- An irregular upper graph has zero one-dimensional Hausdorff measure. -/
theorem hausdorffMeasure_irregularUpperGraph_eq_zero (K : ConvexBody Point)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) :
    Measure.hausdorffMeasure 1 (irregularUpperGraph K o e) = 0 := by
  exact MeasureTheory.hausdorffMeasure_coordinateGraph_nondifferentiable_eq_zero
    (locallyLipschitzOn_upperGraphHeight K o e) o e

private theorem eq_left_or_eq_right_or_mem_Ioo {a b x : ℝ} (hx : x ∈ Set.Icc a b) :
    x = a ∨ x = b ∨ x ∈ Set.Ioo a b := by
  rcases hx.1.eq_or_lt with h | h
  · exact Or.inl h.symm
  rcases hx.2.eq_or_lt with h' | h'
  · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr ⟨h, h'⟩)

private theorem irregularBoundary_subset_graphs_union_corners (K : ConvexBody Point)
    (hK : (interior (K : Set Point)).Nonempty) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) :
    frontier (K : Set Point) \ regularBoundary K ⊆
      irregularUpperGraph K o e ∪ (irregularUpperGraph K o (negCoordinates e) ∪
      (irregularUpperGraph K o (swapCoordinates e) ∪
      (irregularUpperGraph K o (negCoordinates (swapCoordinates e)) ∪
      coordinateCornerSet K o e))) := by
  intro p hp
  have hpK : p ∈ K := by
    change p ∈ (K : Set Point)
    rw [← K.isClosed.closure_eq]
    exact frontier_subset_closure hp.1
  let x := e (p - o) 0
  let y := e (p - o) 1
  have hxIcc : x ∈ Set.Icc (horizontalBounds K o e).1
      (horizontalBounds K o e).2 := by
    rw [← horizontalProjection_eq_Icc K o e]
    exact ⟨p, hpK, rfl⟩
  have hyIcc : y ∈ Set.Icc (horizontalBounds K o (swapCoordinates e)).1
      (horizontalBounds K o (swapCoordinates e)).2 := by
    rw [← horizontalProjection_eq_Icc K o (swapCoordinates e)]
    refine ⟨p, hpK, ?_⟩
    simp [y, swapCoordinates_apply_zero]
  rcases eq_left_or_eq_right_or_mem_Ioo hxIcc with hxleft | hxright | hxint
  · rcases eq_left_or_eq_right_or_mem_Ioo hyIcc with hyleft | hyright | hyint
    · right; right; right; right
      exact ⟨Or.inl (by simpa [x] using hxleft), Or.inl (by simpa [y] using hyleft)⟩
    · right; right; right; right
      exact ⟨Or.inl (by simpa [x] using hxleft), Or.inr (by simpa [y] using hyright)⟩
    · right; right; right; left
      let e' := negCoordinates (swapCoordinates e)
      let z := e' (p - o) 0
      have hzint : z ∈ Set.Ioo (horizontalBounds K o e').1
          (horizontalBounds K o e').2 := by
        rw [horizontalBounds_negCoordinates]
        change -y ∈ Set.Ioo (-(horizontalBounds K o (swapCoordinates e)).2)
          (-(horizontalBounds K o (swapCoordinates e)).1)
        exact ⟨neg_lt_neg hyint.2, neg_lt_neg hyint.1⟩
      have hgraph := eq_negSwapUpperGraph_of_horizontalCoordinate_eq_leftBound
        K o e hpK (by simpa [x] using hxleft)
      refine ⟨z, ⟨hzint, ?_⟩, hgraph.symm⟩
      intro hdiff
      apply hp.2
      rw [hgraph]
      exact upperGraph_mem_regularBoundary K hK o e' hzint hdiff
  · rcases eq_left_or_eq_right_or_mem_Ioo hyIcc with hyleft | hyright | hyint
    · right; right; right; right
      exact ⟨Or.inr (by simpa [x] using hxright), Or.inl (by simpa [y] using hyleft)⟩
    · right; right; right; right
      exact ⟨Or.inr (by simpa [x] using hxright), Or.inr (by simpa [y] using hyright)⟩
    · right; right; left
      let e' := swapCoordinates e
      let z := e' (p - o) 0
      have hzint : z ∈ Set.Ioo (horizontalBounds K o e').1
          (horizontalBounds K o e').2 := by simpa [e', z, y] using hyint
      have hgraph := eq_swapUpperGraph_of_horizontalCoordinate_eq_rightBound
        K o e hpK (by simpa [x] using hxright)
      refine ⟨z, ⟨hzint, ?_⟩, hgraph.symm⟩
      intro hdiff
      apply hp.2
      rw [hgraph]
      exact upperGraph_mem_regularBoundary K hK o e' hzint hdiff
  · obtain ⟨a, ha⟩ := exists_isExteriorNormal_of_mem_frontier K hK hp.1
    have hvertical : e (normalVector a) 1 ≠ 0 := by
      intro hzero
      rcases horizontalCoordinate_eq_endpoint_of_isExteriorNormal_of_vertical_eq_zero
        K o e hpK ha hzero with hleft | hright
      · exact hxint.1.ne' (by simpa [x] using hleft)
      · exact hxint.2.ne (by simpa [x] using hright)
    rcases lt_or_gt_of_ne hvertical with hneg | hpos
    · right; left
      let e' := negCoordinates e
      let z := e' (p - o) 0
      have hzint : z ∈ Set.Ioo (horizontalBounds K o e').1
          (horizontalBounds K o e').2 := by
        rw [horizontalBounds_negCoordinates]
        change -x ∈ Set.Ioo (-(horizontalBounds K o e).2)
          (-(horizontalBounds K o e).1)
        exact ⟨neg_lt_neg hxint.2, neg_lt_neg hxint.1⟩
      have hgraph := eq_upperCoordinateGraph_of_isExteriorNormal_of_pos K o e'
        hpK ha (by simpa [e'] using neg_pos.mpr hneg)
      refine ⟨z, ⟨hzint, ?_⟩, hgraph.symm⟩
      intro hdiff
      apply hp.2
      rw [hgraph]
      exact upperGraph_mem_regularBoundary K hK o e' hzint hdiff
    · left
      have hgraph := eq_upperCoordinateGraph_of_isExteriorNormal_of_pos K o e hpK ha hpos
      refine ⟨x, ⟨hxint, ?_⟩, ?_⟩
      · intro hdiff
        apply hp.2
        rw [hgraph]
        exact upperGraph_mem_regularBoundary K hK o e hxint hdiff
      · simpa [x] using hgraph.symm

/-- The irregular boundary of a planar convex body with nonempty interior has
zero one-dimensional Hausdorff measure. -/
theorem hausdorffMeasure_irregularBoundary_eq_zero (K : ConvexBody Point)
    (hK : (interior (K : Set Point)).Nonempty) :
    Measure.hausdorffMeasure 1
      (frontier (K : Set Point) \ regularBoundary K) = 0 := by
  let e : Point ≃ₗᵢ[ℝ] Point := LinearIsometryEquiv.refl ℝ Point
  let o : Point := 0
  apply measure_mono_null
    (irregularBoundary_subset_graphs_union_corners K hK o e)
  exact MeasureTheory.measure_union_null
    (hausdorffMeasure_irregularUpperGraph_eq_zero K o e)
    (MeasureTheory.measure_union_null
      (hausdorffMeasure_irregularUpperGraph_eq_zero K o (negCoordinates e))
      (MeasureTheory.measure_union_null
        (hausdorffMeasure_irregularUpperGraph_eq_zero K o (swapCoordinates e))
        (MeasureTheory.measure_union_null
          (hausdorffMeasure_irregularUpperGraph_eq_zero K o
            (negCoordinates (swapCoordinates e)))
          (hausdorffMeasure_coordinateCornerSet_eq_zero K o e))))

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Exposed faces and the boundary of a convex body

The exposed faces of a convex body are exactly the sets of boundary points realizing a support
value: each exposed face lies on the boundary, and, when the body has interior, every boundary
point lies on some exposed face.
-/

public section

noncomputable section

namespace MovingSofa

/-- Every boundary point of a convex body with nonempty interior lies on a supporting
exposed face. -/
theorem exists_mem_exposedEdge_of_mem_frontier
    (K : ConvexBody Point) (hK : (interior (K : Set Point)).Nonempty)
    {p : Point} (hp : p ∈ frontier (K : Set Point)) :
    ∃ a : Real.Angle, p ∈ exposedEdge K a := by
  have hpK : p ∈ K := by
    change p ∈ (K : Set Point)
    rw [← K.isClosed.closure_eq]
    exact frontier_subset_closure hp
  obtain ⟨a, ha⟩ := exists_isExteriorNormal_of_mem_frontier K hK hp
  refine ⟨a, hpK, ?_⟩
  change inner ℝ p (normalVector a) = supportValue K a
  apply le_antisymm
  · exact inner_le_supportValue K hpK a
  · obtain ⟨q, hq, hqeq⟩ := exists_mem_inner_eq_supportValue K a
    rw [← hqeq]
    have := ha q hq
    rw [inner_sub_left] at this
    linarith

/-- Every exposed face of a convex body lies on its boundary. -/
theorem exposedEdge_subset_frontier
    (K : ConvexBody Point) (a : Real.Angle) :
    exposedEdge K a ⊆ frontier (K : Set Point) := by
  intro p hp
  rw [mem_frontier_iff_notMem_interior hp.1]
  intro hpint
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hpint
  let z := p + (ε / 2) • normalVector a
  have hzball : z ∈ Metric.ball p ε := by
    simp only [Metric.mem_ball, dist_eq_norm, z, add_sub_cancel_left, norm_smul,
      norm_normalVector, mul_one, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have hzK : z ∈ K := interior_subset (hball hzball)
  have hzle := inner_le_supportValue K hzK a
  have hpEq := hp.2
  change inner ℝ p (normalVector a) = supportValue K a at hpEq
  have hnorm : inner ℝ (normalVector a) (normalVector a) = 1 := by
    induction a using Real.Angle.induction_on with
    | _ a => exact inner_normalVector_self a
  rw [show z = p + (ε / 2) • normalVector a from rfl, inner_add_left,
    real_inner_smul_left, hnorm, hpEq] at hzle
  linarith

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Regular Boundary Helpers
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- A planar convex body with nonempty interior has no segment presentation. -/
theorem not_exists_segmentPresentation_of_interior_nonempty (K : ConvexBody Point)
    (hint : (interior (K : Set Point)).Nonempty) : ¬ ∃ d, IsSegmentPresentation K d := by
  rintro ⟨d, hd⟩
  have htop : affineSpan ℝ (K : Set Point) = ⊤ :=
    K.convex.interior_nonempty_iff_affineSpan_eq_top.mp hint
  have hle : affineSpan ℝ (K : Set Point) ≤ affineSpan ℝ ({d.1, d.2.1} : Set Point) := by
    rw [hd.2.1]
    apply affineSpan_le.2
    exact (affineSpan ℝ ({d.1, d.2.1} : Set Point)).convex.segment_subset
      (subset_affineSpan ℝ _ (by simp)) (subset_affineSpan ℝ _ (by simp))
  rw [htop] at hle
  have heq : affineSpan ℝ ({d.1, d.2.1} : Set Point) = ⊤ := top_unique hle
  have hfin := (collinear_iff_finrank_le_one.mp (collinear_pair ℝ d.1 d.2.1))
  rw [← direction_affineSpan, heq] at hfin
  rw [AffineSubspace.direction_top ℝ Point Point, finrank_top] at hfin
  norm_num [Point, finrank_euclideanSpace_fin] at hfin

/-- A convex body with nonempty interior is not a singleton. -/
theorem not_subsingleton_of_interior_nonempty (K : ConvexBody Point)
    (hint : (interior (K : Set Point)).Nonempty) : ¬ (K : Set Point).Subsingleton := by
  intro hsub
  obtain ⟨p, hp⟩ := K.nonempty
  have hK : (K : Set Point) = {p} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨hp, fun x hx ↦ hsub hx hp⟩
  rw [hK, interior_singleton] at hint
  exact hint.ne_empty rfl

private theorem surfaceAreaMeasure_eq_map_of_interior_nonempty (K : ConvexBody Point)
    (hint : (interior (K : Set Point)).Nonempty) :
    surfaceAreaMeasure K = Measure.map (exteriorNormalAngle K)
      ((Measure.hausdorffMeasure 1).restrict (regularBoundary K)) := by
  have hsub := not_subsingleton_of_interior_nonempty K hint
  have hseg := not_exists_segmentPresentation_of_interior_nonempty K hint
  simp [surfaceAreaMeasure, hsub, hseg]

/-- Surface area measure is finite when the convex body has nonempty interior. -/
theorem isFiniteMeasure_surfaceAreaMeasure_of_interior_nonempty (K : ConvexBody Point)
    (hint : (interior (K : Set Point)).Nonempty) : IsFiniteMeasure (surfaceAreaMeasure K) := by
  rw [surfaceAreaMeasure_eq_map_of_interior_nonempty K hint]
  let μ := (Measure.hausdorffMeasure 1).restrict (regularBoundary K)
  have hμ : μ Set.univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono fun p hp ↦ hp.1)
      (K.hausdorffMeasure_frontier_lt_top hint)
  let _ : IsFiniteMeasure μ := ⟨hμ⟩
  exact Measure.isFiniteMeasure_map μ (exteriorNormalAngle K)

/-- Any extension of the exterior-normal angle from the regular boundary gives
the surface area measure as a pushforward of frontier length. -/
theorem surfaceAreaMeasure_eq_map_frontier_of_eq_on_regularBoundary
    (K : ConvexBody Point) (hK : (interior (K : Set Point)).Nonempty)
    (ν : Point → Real.Angle)
    (hν : ∀ p ∈ regularBoundary K, ν p = exteriorNormalAngle K p) :
    surfaceAreaMeasure K = Measure.map ν
      ((Measure.hausdorffMeasure 1).restrict (frontier (K : Set Point))) := by
  let μ : Measure Point := Measure.hausdorffMeasure 1
  have hregular : regularBoundary K ⊆ frontier (K : Set Point) := fun _ hp ↦ hp.1
  have hae : frontier (K : Set Point) =ᵐ[μ] regularBoundary K := by
    rw [ae_eq_set]
    exact ⟨hausdorffMeasure_irregularBoundary_eq_zero K hK,
      measure_mono_null (fun _ hp ↦ (hp.2 (hregular hp.1)).elim) measure_empty⟩
  have hrestrict : μ.restrict (frontier (K : Set Point)) =
      μ.restrict (regularBoundary K) := Measure.restrict_congr_set hae
  rw [surfaceAreaMeasure_eq_map_of_interior_nonempty K hK, hrestrict]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (measurableSet_regularBoundary K)] with p hp
  exact (hν p hp).symm

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Graph Integral
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace MovingSofa

private theorem exteriorNormalAngle_upperGraph_eq (K : ConvexBody Point)
    (hK : (interior (K : Set Point)).Nonempty) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    {x : ℝ} (hx : x ∈ Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2)
    (hdiff : DifferentiableAt ℝ (upperGraphHeight K o e) x) :
    exteriorNormalAngle K (o + e.symm !₂[x, upperGraphHeight K o e x]) =
      vectorNormalAngle (e.symm !₂[-deriv (upperGraphHeight K o e) x, 1]) := by
  have hp := upperGraph_mem_regularBoundary K hK o e hx hdiff
  have hu := hp.2
  have hn : IsExteriorNormal K (o + e.symm !₂[x, upperGraphHeight K o e x])
      (exteriorNormalAngle K (o + e.symm !₂[x, upperGraphHeight K o e x])) := by
    unfold exteriorNormalAngle
    rw [dite_eq_left hu]
    exact hu.exists.choose_spec
  exact hu.unique hn (upperGraph_deriv_isExteriorNormal K o e hx hdiff)

private theorem coordinate_normalVector_vectorNormalAngle_second
    (e : Point ≃ₗᵢ[ℝ] Point) (m : ℝ) :
    e (normalVector (vectorNormalAngle (e.symm !₂[-m, 1]))) 1 =
      (Real.sqrt (1 + m ^ 2))⁻¹ := by
  let q : Point := e.symm !₂[-m, 1]
  have hq : q ≠ 0 := by
    intro h
    have h1 := congrFun (congrArg WithLp.ofLp (congrArg e h)) 1
    simp [q] at h1
  rw [normalVector_vectorNormalAngle hq, map_smul, PiLp.smul_apply]
  have hnorm : ‖q‖ = Real.sqrt (1 + m ^ 2) := by
    rw [← e.norm_map q, LinearIsometryEquiv.apply_symm_apply, EuclideanSpace.norm_eq]
    congr 1
    simp [Fin.sum_univ_two, Real.norm_eq_abs, pow_two]
    ring
  rw [hnorm]
  simp [q]

private theorem upperGraphSurfaceIntegrand_eq_zero_of_speed_gt
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    (ψ : Real.Angle → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0) {x : ℝ}
    (hx : ε⁻¹ < Real.sqrt (1 + (deriv (upperGraphHeight K o e) x) ^ 2)) :
    upperGraphSurfaceIntegrand K o e ψ x = 0 := by
  rw [upperGraphSurfaceIntegrand, hsupport, zero_mul]
  rw [coordinate_normalVector_vectorNormalAngle_second]
  exact (inv_lt_comm₀ (Real.sqrt_pos.2 (by positivity)) hε).2 hx

private theorem measurable_vectorNormalAngle : Measurable vectorNormalAngle := by
  unfold vectorNormalAngle
  apply Real.Angle.continuous_coe.measurable.comp
  apply Complex.measurable_arg.comp
  have hp0 : Measurable (fun p : Point ↦ p 0) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0).continuous.measurable
  have hp1 : Measurable (fun p : Point ↦ p 1) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 1).continuous.measurable
  have h0 : Measurable (fun p : Point ↦ (p 0 : ℂ)) :=
    Complex.measurable_ofReal.comp hp0
  have h1 : Measurable (fun p : Point ↦ (p 1 : ℂ)) :=
    Complex.measurable_ofReal.comp hp1
  convert h0.add (h1.mul_const Complex.I) using 1
  funext p
  apply Complex.ext <;> simp

private theorem measurable_upperGraphSurfaceIntegrand (K : ConvexBody Point)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) (hψ : Continuous ψ) :
    Measurable (upperGraphSurfaceIntegrand K o e ψ) := by
  unfold upperGraphSurfaceIntegrand
  have hd : Measurable (deriv (upperGraphHeight K o e)) := measurable_deriv _
  have hv : Measurable (fun x ↦ e.symm !₂[-deriv (upperGraphHeight K o e) x, 1]) := by
    fun_prop
  apply (hψ.measurable.comp (measurable_vectorNormalAngle.comp ?_)).mul
    ((measurable_const.add (hd.pow_const 2)).sqrt)
  exact hv

/-- A normal support cutoff gives a uniform bound on the weighted graph density. -/
theorem norm_upperGraphSurfaceIntegrand_le
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    (ψ : Real.Angle → ℝ) {ε M : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0)
    (hM : ∀ t, ‖ψ t‖ ≤ M) (x : ℝ) :
    ‖upperGraphSurfaceIntegrand K o e ψ x‖ ≤ M * ε⁻¹ := by
  have hM0 : 0 ≤ M := (norm_nonneg (ψ 0)).trans (hM 0)
  let s := Real.sqrt (1 + (deriv (upperGraphHeight K o e) x) ^ 2)
  by_cases hs : s ≤ ε⁻¹
  · rw [upperGraphSurfaceIntegrand, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul (hM _) hs (Real.sqrt_nonneg _) hM0
  · rw [upperGraphSurfaceIntegrand_eq_zero_of_speed_gt K o e ψ hε hsupport
      (lt_of_not_ge hs), norm_zero]
    exact mul_nonneg hM0 (le_of_lt (inv_pos.mpr hε))

/-- The weighted surface integrand of an upper graph is integrable on its
horizontal projection interval. -/
theorem integrable_upperGraphSurfaceIntegrand (K : ConvexBody Point)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) (hψ : Continuous ψ)
    {ε : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0) (a b : ℝ) :
    Integrable (upperGraphSurfaceIntegrand K o e ψ) (volume.restrict (Set.Icc a b)) := by
  obtain ⟨t, -, ht⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hψ.norm.continuousOn
  let M := ‖ψ t‖
  have hM (u : Real.Angle) : ‖ψ u‖ ≤ M := ht trivial
  apply (integrable_const (μ := volume.restrict (Set.Icc a b))
    (c := M * ε⁻¹)).mono'
    (measurable_upperGraphSurfaceIntegrand K o e ψ hψ).aestronglyMeasurable
  exact Eventually.of_forall fun x ↦
    norm_upperGraphSurfaceIntegrand_le K o e ψ hε hsupport hM x

private theorem upperCoordinateGraph_mem_frontier (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {x : ℝ}
    (hx : x ∈ Set.Icc (horizontalBounds K o e).1 (horizontalBounds K o e).2) :
    o + e.symm !₂[x, upperGraphHeight K o e x] ∈ frontier (K : Set Point) := by
  have hxproj : x ∈ horizontalProjection K o e := by
    rw [horizontalProjection_eq_Icc]
    exact hx
  let p := o + e.symm !₂[x, upperGraphHeight K o e x]
  have hpK : p ∈ K := upperGraphHeight_mem K o e hxproj
  rw [mem_frontier_iff_notMem_interior hpK]
  intro hpint
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hpint
  let q := p + (r / 2) • e.symm !₂[0, 1]
  have hqp : q ∈ K := interior_subset (hball (by
    rw [Metric.mem_ball, dist_eq_norm]
    rw [show q - p = (r / 2) • e.symm !₂[0, 1] by simp [q], norm_smul,
      e.symm.norm_map, EuclideanSpace.norm_eq]
    simp only [norm_div, Real.norm_eq_abs, sq_abs, Fin.sum_univ_two, Fin.isValue,
      Matrix.cons_val_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, one_pow, zero_add, Real.sqrt_one, mul_one]
    rw [abs_of_pos hr]
    linarith))
  have hqfiber : o + e.symm !₂[x, upperGraphHeight K o e x + r / 2] ∈ K := by
    convert hqp using 1
    apply e.injective
    ext i
    fin_cases i
    · simp [p, q, map_add, map_smul]
    · simp [p, q, map_add, map_smul]
      ring
  have hle := (upperGraphHeight_isGreatest K o e hxproj).2 hqfiber
  linarith

/-- Evaluate an angular weight at the upper graph’s normal direction above a point’s abscissa. -/
def upperGraphWeight (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) (p : Point) : ℝ :=
  ψ (vectorNormalAngle (e.symm !₂[
    -deriv (upperGraphHeight K o e) (e (p - o) 0), 1]))

private theorem measurable_upperGraphWeight (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) (hψ : Continuous ψ) :
    Measurable (upperGraphWeight K o e ψ) := by
  unfold upperGraphWeight
  apply hψ.measurable.comp (measurable_vectorNormalAngle.comp ?_)
  have hx : Measurable (fun p : Point ↦ e (p - o) 0) := by fun_prop
  have hd : Measurable (fun p : Point ↦
      deriv (upperGraphHeight K o e) (e (p - o) 0)) :=
    (measurable_deriv _).comp hx
  fun_prop

private theorem integral_restrict_upperCoordinateGraph_eq_integral
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    (ψ : Real.Angle → ℝ) (hψ : Continuous ψ) {a b : ℝ}
    (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆
      Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2) :
    (∫ p, upperGraphWeight K o e ψ p ∂(Measure.hausdorffMeasure 1).restrict
      ((fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
        Set.Icc a b)) =
      ∫ x in a..b, upperGraphSurfaceIntegrand K o e ψ x := by
  have hlocal : LocallyLipschitzOn (Set.Icc a b) (upperGraphHeight K o e) :=
    (locallyLipschitzOn_upperGraphHeight K o e).mono hsub
  obtain ⟨C, hC⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc hlocal
  rw [MeasureTheory.integral_restrict_coordinateGraph_eq_integral_sqrt_mul hab hC o e
    (measurable_upperGraphWeight K o e ψ hψ)]
  apply intervalIntegral.integral_congr
  intro x _
  unfold upperGraphWeight upperGraphSurfaceIntegrand
  simp only [add_sub_cancel_left, LinearIsometryEquiv.apply_symm_apply, Fin.isValue,
    Matrix.cons_val_zero]
  apply mul_comm

private theorem integral_restrict_upperCoordinateGraph_eq_setIntegral
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    (ψ : Real.Angle → ℝ) (hψ : Continuous ψ) {a b : ℝ}
    (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆
      Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2) :
    (∫ p, upperGraphWeight K o e ψ p ∂(Measure.hausdorffMeasure 1).restrict
      ((fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
        Set.Icc a b)) =
      ∫ x in Set.Icc a b, upperGraphSurfaceIntegrand K o e ψ x := by
  rw [integral_restrict_upperCoordinateGraph_eq_integral K o e ψ hψ hab hsub,
    intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]

private theorem upperCoordinateGraph_image_subset_frontier (K : ConvexBody Point)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {s : Set ℝ}
    (hs : s ⊆ Set.Icc (horizontalBounds K o e).1 (horizontalBounds K o e).2) :
    (fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) '' s ⊆
      frontier (K : Set Point) := by
  rintro _ ⟨x, hx, rfl⟩
  exact upperCoordinateGraph_mem_frontier K o e (hs hx)

private theorem hausdorffMeasure_upperGraph_endpoints_eq_zero (K : ConvexBody Point)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) :
    Measure.hausdorffMeasure 1
      ((fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
        ({(horizontalBounds K o e).1, (horizontalBounds K o e).2} : Set ℝ)) = 0 := by
  let _ := MeasureTheory.Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  apply Set.Finite.measure_zero
  exact (Set.toFinite _).image _

private theorem eventually_innerIcc_nonempty {a b : ℝ} (hab : a < b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      a + 1 / ((n : ℝ) + 1) ≤ b - 1 / ((n : ℝ) + 1) := by
  have hevent := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (Iio_mem_nhds (half_pos (sub_pos.mpr hab)))
  exact hevent.mono fun n hn ↦ by linarith

/-- Integrals over the inner upper graph equal integrals over its coordinate interval. -/
theorem eventually_integral_innerUpperGraph_eq_innerIcc
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    (ψ : Real.Angle → ℝ) (hψ : Continuous ψ)
    (hwidth : (horizontalBounds K o e).1 < (horizontalBounds K o e).2) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (∫ p, upperGraphWeight K o e ψ p ∂(Measure.hausdorffMeasure 1).restrict
        ((fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
          Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
            ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1)))) =
        ∫ x in Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
          ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1)),
          upperGraphSurfaceIntegrand K o e ψ x := by
  filter_upwards [eventually_innerIcc_nonempty hwidth] with n hn
  exact integral_restrict_upperCoordinateGraph_eq_setIntegral K o e ψ hψ hn
    (innerIcc_subset_Ioo _ _ n)

private theorem measurableSet_innerUpperGraph (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (n : ℕ) :
    MeasurableSet
      ((fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
        Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
          ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1))) := by
  let s := Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
    ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1))
  have hs : s ⊆ Set.Ioo (horizontalBounds K o e).1
      (horizontalBounds K o e).2 := innerIcc_subset_Ioo _ _ n
  have hcont : ContinuousOn (upperGraphHeight K o e) s :=
    ((locallyLipschitzOn_upperGraphHeight K o e).mono hs).continuousOn
  exact (isCompact_Icc.image_of_continuousOn (by fun_prop)).measurableSet

private theorem tendsto_innerUpperGraph_indicator_at_regularPoint
    (K : ConvexBody Point) (hK : (interior (K : Set Point)).Nonempty)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0) {p : Point}
    (hp : p ∈ regularBoundary K)
    (hpend : p ∉ (fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
      ({(horizontalBounds K o e).1, (horizontalBounds K o e).2} : Set ℝ))
    (hpirr : p ∉ irregularUpperGraph K o e) :
    Filter.Tendsto (fun n : ℕ ↦
      (((fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
        Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
          ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1))).indicator
            (upperGraphWeight K o e ψ) p)) Filter.atTop
      (nhds (ψ (exteriorNormalAngle K p))) := by
  let a := exteriorNormalAngle K p
  have ha : IsExteriorNormal K p a := by
    dsimp only [a]
    unfold exteriorNormalAngle
    rw [dite_eq_left hp.2]
    exact hp.2.exists.choose_spec
  have hpK : p ∈ K := by
    change p ∈ (K : Set Point)
    rw [← K.isClosed.closure_eq]
    exact frontier_subset_closure hp.1
  by_cases hψa : ψ a = 0
  · apply tendsto_const_nhds.congr'
    filter_upwards [] with n
    by_cases hpn : p ∈ (fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
        Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
          ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1))
    · obtain ⟨x, hx, rfl⟩ := hpn
      have hxint := innerIcc_subset_Ioo (horizontalBounds K o e).1
        (horizontalBounds K o e).2 n hx
      have hdiff : DifferentiableAt ℝ (upperGraphHeight K o e) x := by
        by_contra hndiff
        exact hpirr ⟨x, ⟨hxint, hndiff⟩, rfl⟩
      have hmem : (o + e.symm !₂[x, upperGraphHeight K o e x]) ∈
          (fun y ↦ o + e.symm !₂[y, upperGraphHeight K o e y] : ℝ → Point) ''
            Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
              ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1)) := ⟨x, hx, rfl⟩
      rw [Set.indicator_of_mem hmem]
      unfold upperGraphWeight
      simp only [add_sub_cancel_left, LinearIsometryEquiv.apply_symm_apply, Fin.isValue,
        Matrix.cons_val_zero]
      rw [← exteriorNormalAngle_upperGraph_eq K hK o e hxint hdiff]
    · change ψ a = _
      rw [Set.indicator]
      simp only [hpn, ↓reduceIte]
      exact hψa
  · have hcoord : ε ≤ e (normalVector a) 1 := by
      apply le_of_not_gt
      exact fun h ↦ hψa (hsupport a h)
    have hpos : 0 < e (normalVector a) 1 := hε.trans_le hcoord
    have hgraph := eq_upperCoordinateGraph_of_isExteriorNormal_of_pos K o e hpK ha hpos
    let x := e (p - o) 0
    have hxproj : x ∈ horizontalProjection K o e := ⟨p, hpK, rfl⟩
    have hxIcc : x ∈ Set.Icc (horizontalBounds K o e).1
        (horizontalBounds K o e).2 := by
      rw [← horizontalProjection_eq_Icc]
      exact hxproj
    have hxneleft : x ≠ (horizontalBounds K o e).1 := by
      intro hx
      apply hpend
      refine ⟨x, by simp [hx], ?_⟩
      exact hgraph.symm
    have hxneright : x ≠ (horizontalBounds K o e).2 := by
      intro hx
      apply hpend
      refine ⟨x, by simp [hx], ?_⟩
      exact hgraph.symm
    have hxint : x ∈ Set.Ioo (horizontalBounds K o e).1
        (horizontalBounds K o e).2 :=
      ⟨lt_of_le_of_ne hxIcc.1 (Ne.symm hxneleft), lt_of_le_of_ne hxIcc.2 hxneright⟩
    have hdiff : DifferentiableAt ℝ (upperGraphHeight K o e) x := by
      by_contra hndiff
      apply hpirr
      refine ⟨x, ⟨hxint, hndiff⟩, ?_⟩
      exact hgraph.symm
    have hweight : upperGraphWeight K o e ψ p = ψ a := by
      unfold upperGraphWeight
      dsimp only [x]
      have haeq : a = vectorNormalAngle
          (e.symm !₂[-deriv (upperGraphHeight K o e) (e (p - o) 0), 1]) := by
        have he := exteriorNormalAngle_upperGraph_eq K hK o e hxint hdiff
        dsimp only [x] at he
        calc
          a = exteriorNormalAngle K p := rfl
          _ = exteriorNormalAngle K
              (o + e.symm !₂[e (p - o) 0, upperGraphHeight K o e (e (p - o) 0)]) :=
            congrArg (exteriorNormalAngle K) hgraph
          _ = _ := he
      rw [haeq]
    have hev := eventually_mem_innerIcc_of_mem_Ioo hxint
    apply tendsto_const_nhds.congr'
    exact hev.mono fun n hn ↦ by
      have hmem : p ∈ (fun y ↦ o + e.symm !₂[y, upperGraphHeight K o e y] : ℝ → Point) ''
          Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
            ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1)) := ⟨x, hn, hgraph.symm⟩
      change ψ (exteriorNormalAngle K p) = _
      simp only [Set.indicator, hmem, ↓reduceIte, hweight]
      rfl

/-- Weighted integrals over compact inner upper graphs converge to the weighted
integral over the full frontier. -/
theorem tendsto_integral_innerUpperGraph
    (K : ConvexBody Point) (hK : (interior (K : Set Point)).Nonempty)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) (hψ : Continuous ψ)
    {ε : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0) :
    Filter.Tendsto (fun n : ℕ ↦
      ∫ p, upperGraphWeight K o e ψ p ∂(Measure.hausdorffMeasure 1).restrict
        ((fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
          Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
            ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1)))) Filter.atTop
      (nhds (∫ p in frontier (K : Set Point), ψ (exteriorNormalAngle K p)
        ∂Measure.hausdorffMeasure 1)) := by
  let μ : Measure Point := Measure.hausdorffMeasure 1
  let t := frontier (K : Set Point)
  let g : ℕ → Set Point := fun n ↦
    (fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
      Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
        ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1))
  obtain ⟨u, -, hu⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hψ.norm.continuousOn
  let M := ‖ψ u‖
  have hM (v : Real.Angle) : ‖ψ v‖ ≤ M := hu trivial
  have hM0 : 0 ≤ M := norm_nonneg _
  have hgt (n : ℕ) : g n ⊆ t :=
    upperCoordinateGraph_image_subset_frontier K o e
      ((innerIcc_subset_Ioo _ _ n).trans Set.Ioo_subset_Icc_self)
  have hgmeas (n : ℕ) : MeasurableSet (g n) := measurableSet_innerUpperGraph K o e n
  have hFmeas (n : ℕ) : AEStronglyMeasurable
      ((g n).indicator (upperGraphWeight K o e ψ)) μ :=
    (measurable_upperGraphWeight K o e ψ hψ).aestronglyMeasurable.indicator (hgmeas n)
  have hbound (n : ℕ) : ∀ᵐ p ∂μ,
      ‖(g n).indicator (upperGraphWeight K o e ψ) p‖ ≤ t.indicator (fun _ ↦ M) p :=
    Filter.Eventually.of_forall fun p ↦ by
      by_cases hp : p ∈ g n
      · have hpt := hgt n hp
        rw [Set.indicator_of_mem hp, Set.indicator_of_mem hpt]
        exact hM _
      · rw [Set.indicator]
        simp only [hp, ↓reduceIte, norm_zero]
        by_cases hpt : p ∈ t <;> simp [hpt, hM0]
  have hboundInt : Integrable (t.indicator fun _ ↦ M) μ := by
    apply MeasureTheory.IntegrableOn.integrable_indicator
    · exact MeasureTheory.integrableOn_const
        (lt_top_iff_ne_top.mp (K.hausdorffMeasure_frontier_lt_top hK))
    · exact measurableSet_frontier
  have hae : t =ᵐ[μ] regularBoundary K := by
    rw [ae_eq_set]
    exact ⟨hausdorffMeasure_irregularBoundary_eq_zero K hK,
      measure_mono_null (fun _ hp ↦ (hp.2 hp.1.1).elim) measure_empty⟩
  have hpreg : ∀ᵐ p ∂μ, p ∈ t → p ∈ regularBoundary K := by
    filter_upwards [hae] with p hp
    exact fun hpt ↦ hp.mp hpt
  have hpend : ∀ᵐ p ∂μ, p ∉
      (fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
        ({(horizontalBounds K o e).1, (horizontalBounds K o e).2} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp (hausdorffMeasure_upperGraph_endpoints_eq_zero K o e)
  have hpirr : ∀ᵐ p ∂μ, p ∉ irregularUpperGraph K o e :=
    measure_eq_zero_iff_ae_notMem.mp (hausdorffMeasure_irregularUpperGraph_eq_zero K o e)
  have hlim : ∀ᵐ p ∂μ, Filter.Tendsto
      (fun n ↦ (g n).indicator (upperGraphWeight K o e ψ) p) Filter.atTop
      (nhds (t.indicator (fun p ↦ ψ (exteriorNormalAngle K p)) p)) := by
    filter_upwards [hpreg, hpend, hpirr] with p hpreg hpend hpirr
    by_cases hpt : p ∈ t
    · rw [Set.indicator_of_mem hpt]
      exact tendsto_innerUpperGraph_indicator_at_regularPoint K hK o e ψ hε hsupport
        (hpreg hpt) hpend hpirr
    · simp only [Set.indicator, hpt, ↓reduceIte]
      apply tendsto_const_nhds.congr'
      filter_upwards [] with n
      have hpgn : p ∉ g n := fun h ↦ hpt (hgt n h)
      simp [hpgn]
  have ht := MeasureTheory.tendsto_integral_of_dominated_convergence (μ := μ)
    (t.indicator fun _ ↦ M) hFmeas hboundInt hbound hlim
  have htarget : (∫ p, t.indicator (fun p ↦ ψ (exteriorNormalAngle K p)) p ∂μ) =
      ∫ p in t, ψ (exteriorNormalAngle K p) ∂μ := by
    rw [MeasureTheory.integral_indicator measurableSet_frontier]
  rw [← htarget]
  simpa only [μ, g, MeasureTheory.integral_indicator, hgmeas] using ht

/-- A planar convex body with nonempty interior has distinct horizontal bounds
in every isometric coordinate frame. -/
theorem horizontalBounds_lt_of_interior_nonempty (K : ConvexBody Point)
    (hK : (interior (K : Set Point)).Nonempty) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) :
    (horizontalBounds K o e).1 < (horizontalBounds K o e).2 := by
  obtain ⟨z, hz⟩ := hK
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  let v := e.symm (normalVector 0)
  let q := z + (ε / 2) • v
  have hq : q ∈ K := interior_subset (hball (by
    rw [Metric.mem_ball, dist_eq_norm]
    rw [show q - z = (ε / 2) • v by simp [q], norm_smul]
    simp only [v, e.symm.norm_map, norm_normalVector, mul_one, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    linarith))
  have hzI : e (z - o) 0 ∈ Set.Icc (horizontalBounds K o e).1
      (horizontalBounds K o e).2 := by
    rw [← horizontalProjection_eq_Icc]
    exact ⟨z, interior_subset hz, rfl⟩
  have hqI : e (q - o) 0 ∈ Set.Icc (horizontalBounds K o e).1
      (horizontalBounds K o e).2 := by
    rw [← horizontalProjection_eq_Icc]
    exact ⟨q, hq, rfl⟩
  have hcoord : e (q - o) 0 = e (z - o) 0 + ε / 2 := by
    rw [show q - o = (z - o) + (ε / 2) • v by simp [q]; module]
    simp [v, normalVector, frame]
  linarith [hzI.1, hqI.2]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Construction
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

theorem surfaceAreaMeasure_construction (K : ConvexBody Point) :
    IsFiniteMeasure (surfaceAreaMeasure K) ∧
    ((K : Set Point).Subsingleton → surfaceAreaMeasure K = 0) ∧
    (∀ d, IsSegmentPresentation K d → surfaceAreaMeasure K =
      ENNReal.ofReal (dist d.1 d.2.1) •
        (Measure.dirac d.2.2 + Measure.dirac (d.2.2 + ((Real.pi : ℝ) : Real.Angle)))) ∧
    ((interior (K : Set Point)).Nonempty →
      Measure.hausdorffMeasure 1 (frontier (K : Set Point)) < ⊤ ∧
      Measure.hausdorffMeasure 1 (frontier (K : Set Point) \ regularBoundary K) = 0 ∧
      ∀ ν : Point → Real.Angle, (∀ p ∈ regularBoundary K, ν p = exteriorNormalAngle K p) →
        surfaceAreaMeasure K = Measure.map ν
          ((Measure.hausdorffMeasure 1).restrict (frontier (K : Set Point)))) ∧
    (∀ (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ), Continuous ψ →
      ∀ ε : ℝ, 0 < ε → (∀ t, e (normalVector t) 1 < ε → ψ t = 0) →
      ((horizontalBounds K o e).1 < (horizontalBounds K o e).2 →
        Integrable (upperGraphSurfaceIntegrand K o e ψ)
          (volume.restrict (Set.Icc (horizontalBounds K o e).1 (horizontalBounds K o e).2)) ∧
        (∫ t, ψ t ∂surfaceAreaMeasure K) =
          ∫ x in Set.Icc (horizontalBounds K o e).1 (horizontalBounds K o e).2,
            upperGraphSurfaceIntegrand K o e ψ x) ∧
      ((horizontalBounds K o e).1 = (horizontalBounds K o e).2 →
        (∫ t, ψ t ∂surfaceAreaMeasure K) = 0)) := by
  by_cases hsub : (K : Set Point).Subsingleton
  · refine ⟨isFiniteMeasure_surfaceAreaMeasure_of_subsingleton K hsub,
      fun _ ↦ surfaceAreaMeasure_eq_zero_of_subsingleton K hsub, ?_, ?_, ?_⟩
    · intro d hd
      exact (not_subsingleton_of_isSegmentPresentation K hd hsub).elim
    · intro hint
      obtain ⟨p, hp⟩ := K.nonempty
      have hset : (K : Set Point) = {p} :=
        Set.eq_singleton_iff_unique_mem.mpr ⟨hp, fun x hx ↦ hsub hx hp⟩
      rw [hset, interior_singleton] at hint
      exact hint.ne_empty rfl |>.elim
    · intro o e ψ _ ε _ _
      have hbounds := horizontalBounds_eq_of_subsingleton K hsub o e
      constructor
      · intro hlt
        exact (hlt.ne hbounds).elim
      · intro _
        exact surfaceAreaMeasure_integral_eq_zero_of_subsingleton K hsub ψ
  · by_cases hint : (interior (K : Set Point)).Nonempty
    · refine ⟨isFiniteMeasure_surfaceAreaMeasure_of_interior_nonempty K hint,
        fun hs ↦ (not_subsingleton_of_interior_nonempty K hint hs).elim, ?_, ?_, ?_⟩
      · intro d hd
        exact (not_exists_segmentPresentation_of_interior_nonempty K hint ⟨d, hd⟩).elim
      · intro _
        refine ⟨K.hausdorffMeasure_frontier_lt_top hint, ?_, ?_⟩
        · exact hausdorffMeasure_irregularBoundary_eq_zero K hint
        · intro ν hν
          exact surfaceAreaMeasure_eq_map_frontier_of_eq_on_regularBoundary K hint ν hν
      · intro o e ψ hψ ε hε hsupport
        constructor
        · intro hwidth
          have hintg := integrable_upperGraphSurfaceIntegrand K o e ψ hψ hε hsupport
            (horizontalBounds K o e).1 (horizontalBounds K o e).2
          refine ⟨hintg, ?_⟩
          rw [surfaceAreaMeasure_eq_map_frontier_of_eq_on_regularBoundary K hint
            (exteriorNormalAngle K) (fun _ _ ↦ rfl)]
          rw [MeasureTheory.integral_map]
          · apply tendsto_nhds_unique
              (tendsto_integral_innerUpperGraph K hint o e ψ hψ hε hsupport)
            apply (tendsto_integral_innerIcc hintg).congr'
            filter_upwards [eventually_integral_innerUpperGraph_eq_innerIcc
              K o e ψ hψ hwidth] with n hn
            exact hn.symm
          · have hae : frontier (K : Set Point) =ᵐ[Measure.hausdorffMeasure 1]
                regularBoundary K := by
              rw [ae_eq_set]
              exact ⟨hausdorffMeasure_irregularBoundary_eq_zero K hint,
                measure_mono_null (fun _ hp ↦ (hp.2 hp.1.1).elim) measure_empty⟩
            have hrestrict : (Measure.hausdorffMeasure 1).restrict
                (frontier (K : Set Point)) =
                (Measure.hausdorffMeasure 1).restrict (regularBoundary K) :=
              Measure.restrict_congr_set hae
            rw [hrestrict]
            exact aemeasurable_exteriorNormalAngle_restrict_regularBoundary K
              (Measure.hausdorffMeasure 1)
          · exact hψ.aestronglyMeasurable
        · intro hwidth
          exact ((horizontalBounds_lt_of_interior_nonempty K hint o e).ne hwidth).elim
    · have hinterior : interior (K : Set Point) = ∅ := Set.not_nonempty_iff_eq_empty.mp hint
      have hseg := exists_segmentPresentation_of_interior_empty K hsub hinterior
      refine ⟨isFiniteMeasure_surfaceAreaMeasure_of_segmentPresentation K hseg.choose_spec,
        fun hs ↦ (hsub hs).elim, ?_, ?_, ?_⟩
      · intro d hd
        exact surfaceAreaMeasure_eq_segmentPresentation K d hd
      · exact fun hi ↦ (hint hi).elim
      · intro o e ψ _ ε hε hsupport
        constructor
        · intro hbounds
          exact segment_graph_formula K o e ψ hε hsupport hseg.choose hseg.choose_spec hbounds
        · intro hbounds
          exact segment_integral_eq_zero_of_horizontalBounds_eq K o e ψ ε hε hsupport
            hseg.choose hseg.choose_spec hbounds

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Graph Convergence
-/

public section

noncomputable section

open Filter
open MeasureTheory
open scoped Topology

namespace MovingSofa

/-- The angle of a planar vector varies continuously away from zero. -/
theorem continuousAt_vectorNormalAngle {p : Point} (hp : p ≠ 0) :
    ContinuousAt vectorNormalAngle p := by
  have hz : (⟨p 0, p 1⟩ : ℂ) ≠ 0 := by
    intro h
    apply hp
    ext i
    fin_cases i
    · exact congrArg Complex.re h
    · exact congrArg Complex.im h
  have hc : Continuous (fun q : Point ↦ (⟨q 0, q 1⟩ : ℂ)) := by
    have h : Continuous (fun q : Point ↦ (q 0 : ℂ) + (q 1 : ℂ) * Complex.I) := by
      fun_prop
    convert h using 1
    funext q
    apply Complex.ext <;> simp
  exact (Complex.continuousAt_arg_coe_angle hz).comp
    (f := fun q : Point ↦ (⟨q 0, q 1⟩ : ℂ)) hc.continuousAt

/-- The weighted upper-graph surface density is continuous as a function of slope. -/
theorem continuous_surfaceDensity_of_slope (e : Point ≃ₗᵢ[ℝ] Point)
    {ψ : Real.Angle → ℝ} (hψ : Continuous ψ) :
    Continuous (fun r : ℝ ↦ ψ (vectorNormalAngle (e.symm !₂[-r, 1])) *
      Real.sqrt (1 + r ^ 2)) := by
  have hv : Continuous (fun r : ℝ ↦ vectorNormalAngle (e.symm !₂[-r, 1])) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    have hne : e.symm !₂[-r, 1] ≠ 0 := by
      intro h
      have h1 := congrArg (fun p : Point ↦ e p 1) h
      simp at h1
    apply (continuousAt_vectorNormalAngle hne).comp
      (f := fun r : ℝ ↦ e.symm !₂[-r, 1])
    fun_prop
  exact (hψ.comp hv).mul (by fun_prop)

private theorem ae_differentiableAt_upperGraphHeight (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) :
    ∀ᵐ x : ℝ, x ∈ Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2 →
      DifferentiableAt ℝ (upperGraphHeight K o e) x := by
  let a := (horizontalBounds K o e).1
  let b := (horizontalBounds K o e).2
  let δ : ℕ → ℝ := fun m ↦ 1 / ((m : ℝ) + 1)
  have hδpos (m : ℕ) : 0 < δ m := by positivity
  have hcompact (m : ℕ) : IsCompact (Set.Icc (a + δ m) (b - δ m)) := isCompact_Icc
  have hsub (m : ℕ) : Set.Icc (a + δ m) (b - δ m) ⊆ Set.Ioo a b := by
    intro x hx
    exact ⟨lt_of_lt_of_le (lt_add_of_pos_right a (hδpos m)) hx.1,
      lt_of_le_of_lt hx.2 (sub_lt_self b (hδpos m))⟩
  have hae (m : ℕ) : ∀ᵐ x : ℝ,
      x ∈ Set.Ioo (a + δ m) (b - δ m) →
        DifferentiableAt ℝ (upperGraphHeight K o e) x := by
    obtain ⟨C, hC⟩ :=
      ((locallyLipschitzOn_upperGraphHeight K o e).mono (hsub m)).exists_lipschitzOnWith_of_compact
        (hcompact m)
    filter_upwards [hC.ae_differentiableWithinAt_of_mem_of_real] with x hdiff hx
    exact (hdiff ⟨hx.1.le, hx.2.le⟩).differentiableAt (Icc_mem_nhds hx.1 hx.2)
  have hall : ∀ᵐ x : ℝ, ∀ m, x ∈ Set.Ioo (a + δ m) (b - δ m) →
      DifferentiableAt ℝ (upperGraphHeight K o e) x :=
    MeasureTheory.ae_all_iff.mpr hae
  filter_upwards [hall] with x hxall hx
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hevent : ∀ᶠ m in atTop, δ m < x - a ∧ δ m < b - x :=
    ((hδ.eventually_lt_const (sub_pos.mpr hx.1)).and
      (hδ.eventually_lt_const (sub_pos.mpr hx.2)))
  obtain ⟨m, hm⟩ := hevent.exists
  apply hxall m
  constructor <;> linarith [hm.1, hm.2]

private theorem exists_tendsto_points_of_mem_of_hausdorffDist
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) {p : Point} (hp : p ∈ L) :
    ∃ q : ℕ → Point, (∀ n, q n ∈ K n) ∧ Tendsto q atTop (𝓝 p) := by
  have hnear (n : ℕ) : ∃ q ∈ (K n : Set Point),
      dist p q < Metric.hausdorffDist (K n : Set Point) (L : Set Point) +
        1 / ((n : ℝ) + 1) := by
    obtain ⟨q, hq, hd⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt'
      (r := Metric.hausdorffDist (K n : Set Point) (L : Set Point) +
        1 / ((n : ℝ) + 1)) hp
      (by linarith [show 0 < 1 / ((n : ℝ) + 1) by positivity])
      (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        (K n).nonempty L.nonempty (K n).isCompact.isBounded L.isCompact.isBounded)
    exact ⟨q, hq, by simpa [dist_comm] using hd⟩
  choose q hqK hqdist using hnear
  refine ⟨q, hqK, ?_⟩
  have hsum : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point) + 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [add_zero] using hlim.add tendsto_one_div_add_atTop_nhds_zero_nat
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ dist_nonneg) _ hsum
  intro n
  simpa [dist_comm] using (hqdist n).le

private theorem exists_horizontal_side_points (L : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {x : ℝ}
    (hx : x ∈ Set.Ioo (horizontalBounds L o e).1 (horizontalBounds L o e).2) :
    ∃ l ∈ (L : Set Point), ∃ r ∈ (L : Set Point),
      e (l - o) 0 < x ∧ x < e (r - o) 0 := by
  let a := (horizontalBounds L o e).1
  let b := (horizontalBounds L o e).2
  have hlcoord : (a + x) / 2 ∈ horizontalProjection L o e := by
    rw [horizontalProjection_eq_Icc]
    dsimp [a, b]
    constructor <;> linarith [hx.1, hx.2]
  have hrcoord : (x + b) / 2 ∈ horizontalProjection L o e := by
    rw [horizontalProjection_eq_Icc]
    dsimp [a, b]
    constructor <;> linarith [hx.1, hx.2]
  obtain ⟨l, hl, hleq⟩ := hlcoord
  obtain ⟨r, hr, hreq⟩ := hrcoord
  refine ⟨l, hl, r, hr, ?_, ?_⟩
  · change e (l - o) 0 = (a + x) / 2 at hleq
    rw [hleq]
    dsimp [a]
    linarith [hx.1]
  · change e (r - o) 0 = (x + b) / 2 at hreq
    rw [hreq]
    dsimp [b]
    linarith [hx.2]

/-- Points on an interior horizontal fiber can be approximated within the same fibers. -/
theorem exists_tendsto_points_with_horizontal_coordinate
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    {p : Point} (hp : p ∈ L)
    (hpint : e (p - o) 0 ∈ Set.Ioo (horizontalBounds L o e).1
      (horizontalBounds L o e).2) :
    ∃ q : ℕ → Point, (∀ n, q n ∈ K n) ∧ Tendsto q atTop (𝓝 p) ∧
      ∀ᶠ n in atTop, e (q n - o) 0 = e (p - o) 0 := by
  let c : Point → ℝ := fun z ↦ e (z - o) 0
  have hc : Continuous c := by
    exact (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).comp
      (e.continuous.comp (continuous_id.sub continuous_const))
  have hc_lineMap (a b : Point) (t : ℝ) :
      c (AffineMap.lineMap a b t) = (1 - t) * c a + t * c b := by
    dsimp [c]
    rw [AffineMap.lineMap_apply_module]
    simp only [map_sub, map_add, map_smul, PiLp.sub_apply, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul]
    ring
  obtain ⟨l, hlL, r, hrL, hl, hr⟩ := exists_horizontal_side_points L o e hpint
  obtain ⟨pn, hpnK, hpn⟩ := exists_tendsto_points_of_mem_of_hausdorffDist K L hlim hp
  obtain ⟨ln, hlnK, hln⟩ := exists_tendsto_points_of_mem_of_hausdorffDist K L hlim hlL
  obtain ⟨rn, hrnK, hrn⟩ := exists_tendsto_points_of_mem_of_hausdorffDist K L hlim hrL
  let x := c p
  let tR : ℕ → ℝ := fun n ↦ (x - c (pn n)) / (c (rn n) - c (pn n))
  let tL : ℕ → ℝ := fun n ↦ (c (pn n) - x) / (c (pn n) - c (ln n))
  let qR : ℕ → Point := fun n ↦ AffineMap.lineMap (pn n) (rn n) (tR n)
  let qL : ℕ → Point := fun n ↦ AffineMap.lineMap (pn n) (ln n) (tL n)
  let corrected : ℕ → Point := fun n ↦ if c (pn n) ≤ x then qR n else qL n
  let good : ℕ → Prop := fun n ↦ c (ln n) < x ∧ x < c (rn n)
  let q : ℕ → Point := fun n ↦ if good n then corrected n else pn n
  have hcp : Tendsto (fun n ↦ c (pn n)) atTop (𝓝 (c p)) := (hc.tendsto p).comp hpn
  have hcl : Tendsto (fun n ↦ c (ln n)) atTop (𝓝 (c l)) := (hc.tendsto l).comp hln
  have hcr : Tendsto (fun n ↦ c (rn n)) atTop (𝓝 (c r)) := (hc.tendsto r).comp hrn
  have htR : Tendsto tR atTop (𝓝 0) := by
    have hden : c r - c p ≠ 0 := by
      dsimp [c] at hr
      linarith
    have hxlim : Tendsto (fun _ : ℕ ↦ x) atTop (𝓝 x) := tendsto_const_nhds
    change Tendsto ((fun n ↦ x - c (pn n)) /
      fun n ↦ c (rn n) - c (pn n)) atTop (𝓝 0)
    simpa [x] using (hxlim.sub hcp).div (hcr.sub hcp) hden
  have htL : Tendsto tL atTop (𝓝 0) := by
    have hden : c p - c l ≠ 0 := by
      dsimp [c] at hl
      linarith
    have hxlim : Tendsto (fun _ : ℕ ↦ x) atTop (𝓝 x) := tendsto_const_nhds
    change Tendsto ((fun n ↦ c (pn n) - x) /
      fun n ↦ c (pn n) - c (ln n)) atTop (𝓝 0)
    simpa [x] using (hcp.sub hxlim).div (hcp.sub hcl) hden
  have hqR : Tendsto qR atTop (𝓝 p) := by
    simpa [qR] using hpn.lineMap hrn htR
  have hqL : Tendsto qL atTop (𝓝 p) := by
    simpa [qL] using hpn.lineMap hln htL
  have hcorrected : Tendsto corrected atTop (𝓝 p) := by
    exact hqR.if' hqL
  have hq : Tendsto q atTop (𝓝 p) := by
    exact hcorrected.if' hpn
  have hgood : ∀ᶠ n in atTop, good n := by
    filter_upwards [hcl.eventually_lt tendsto_const_nhds hl,
      tendsto_const_nhds.eventually_lt hcr hr] with n hnl hnr
    exact ⟨hnl, hnr⟩
  refine ⟨q, ?_, hq, ?_⟩
  · intro n
    by_cases hgn : good n
    · simp only [q, hgn, ite_true, corrected]
      dsimp [good] at hgn
      by_cases hpnx : c (pn n) ≤ x
      · simp only [hpnx, ite_true, qR]
        apply (K n).convex.lineMap_mem (hpnK n) (hrnK n)
        constructor
        · exact div_nonneg (sub_nonneg.mpr hpnx) (sub_nonneg.mpr (le_trans hpnx hgn.2.le))
        · apply (div_le_one (sub_pos.mpr (lt_of_le_of_lt hpnx hgn.2))).mpr
          linarith
      · simp only [hpnx, ite_false, qL]
        apply (K n).convex.lineMap_mem (hpnK n) (hlnK n)
        constructor
        · exact div_nonneg (sub_nonneg.mpr (le_of_not_ge hpnx))
            (sub_nonneg.mpr (le_trans hgn.1.le (le_of_not_ge hpnx)))
        · apply (div_le_one (sub_pos.mpr (lt_of_lt_of_le hgn.1 (le_of_not_ge hpnx)))).mpr
          linarith
    · simp [q, hgn, hpnK n]
  · filter_upwards [hgood] with n hgn
    simp only [q, hgn, ite_true, corrected]
    dsimp [good] at hgn
    by_cases hpnx : c (pn n) ≤ x
    · simp only [hpnx, ite_true, qR, tR]
      rw [show e (AffineMap.lineMap (pn n) (rn n)
          ((x - c (pn n)) / (c (rn n) - c (pn n))) - o) 0 =
          c (AffineMap.lineMap (pn n) (rn n)
            ((x - c (pn n)) / (c (rn n) - c (pn n)))) by rfl]
      rw [hc_lineMap]
      change _ = x
      field_simp [ne_of_gt (sub_pos.mpr (lt_of_le_of_lt hpnx hgn.2))]
      ring
    · simp only [hpnx, ite_false, qL, tL]
      rw [show e (AffineMap.lineMap (pn n) (ln n)
          ((c (pn n) - x) / (c (pn n) - c (ln n))) - o) 0 =
          c (AffineMap.lineMap (pn n) (ln n)
            ((c (pn n) - x) / (c (pn n) - c (ln n)))) by rfl]
      rw [hc_lineMap]
      change _ = x
      field_simp [ne_of_gt (sub_pos.mpr (lt_of_lt_of_le hgn.1 (le_of_not_ge hpnx)))]
      ring

/-- A varying point of the approximating bodies is asymptotically close to the limit body. -/
private theorem exists_points_in_limit_tendsto_dist_zero
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) (p : ℕ → Point) (hp : ∀ n, p n ∈ K n) :
    ∃ q : ℕ → Point, (∀ n, q n ∈ L) ∧
      Tendsto (fun n ↦ dist (p n) (q n)) atTop (𝓝 0) := by
  have hnear (n : ℕ) : ∃ q ∈ (L : Set Point),
      dist (p n) q < Metric.hausdorffDist (K n : Set Point) (L : Set Point) +
        1 / ((n : ℝ) + 1) := by
    obtain ⟨q, hq, hd⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt
      (r := Metric.hausdorffDist (K n : Set Point) (L : Set Point) +
        1 / ((n : ℝ) + 1)) (hp n)
      (by linarith [show 0 < 1 / ((n : ℝ) + 1) by positivity])
      (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        (K n).nonempty L.nonempty (K n).isCompact.isBounded L.isCompact.isBounded)
    exact ⟨q, hq, hd⟩
  choose q hqL hqdist using hnear
  refine ⟨q, hqL, ?_⟩
  have hsum : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point) + 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [add_zero] using hlim.add tendsto_one_div_add_atTop_nhds_zero_nat
  apply squeeze_zero (fun _ ↦ dist_nonneg) _ hsum
  exact fun n ↦ (hqdist n).le

/-- Upper graph heights converge at every interior point of the limit projection. -/
theorem tendsto_upperGraphHeight_of_hausdorffDist
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    {x : ℝ} (hx : x ∈ Set.Ioo (horizontalBounds L o e).1
      (horizontalBounds L o e).2) :
    Tendsto (fun n ↦ upperGraphHeight (K n) o e x) atTop
      (𝓝 (upperGraphHeight L o e x)) := by
  classical
  let cx : Point → ℝ := fun p ↦ e (p - o) 0
  let cy : Point → ℝ := fun p ↦ e (p - o) 1
  have reconstruct (p : Point) : o + e.symm !₂[cx p, cy p] = p := by
    dsimp [cx, cy]
    rw [← e.injective.eq_iff]
    ext i
    fin_cases i <;> simp
  have hxproj : x ∈ horizontalProjection L o e := by
    rw [horizontalProjection_eq_Icc]
    exact ⟨hx.1.le, hx.2.le⟩
  let pTop := o + e.symm !₂[x, upperGraphHeight L o e x]
  have hpTop : pTop ∈ L := upperGraphHeight_mem L o e hxproj
  have hcxTop : cx pTop = x := by simp [cx, pTop]
  have hcyTop : cy pTop = upperGraphHeight L o e x := by simp [cy, pTop]
  have hpTopInt : cx pTop ∈ Set.Ioo (horizontalBounds L o e).1
      (horizontalBounds L o e).2 := by simpa [hcxTop] using hx
  obtain ⟨q, hqK, hq, hqx⟩ :=
    exists_tendsto_points_with_horizontal_coordinate K L hlim o e hpTop hpTopInt
  have hcyq : Tendsto (fun n ↦ cy (q n)) atTop
      (𝓝 (upperGraphHeight L o e x)) := by
    have hcy : Continuous cy := by
      exact (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1).comp
        (e.continuous.comp (continuous_id.sub continuous_const))
    change Tendsto (cy ∘ q) atTop (𝓝 (upperGraphHeight L o e x))
    simpa [hcyTop] using (hcy.tendsto pTop).comp hq
  have hqcx : ∀ᶠ n in atTop, cx (q n) = x := by
    filter_upwards [hqx] with n hnx
    dsimp [cx]
    rw [hnx]
    exact hcxTop
  have hqproj : ∀ᶠ n in atTop, x ∈ horizontalProjection (K n) o e := by
    filter_upwards [hqcx] with n hnx
    refine ⟨q n, hqK n, ?_⟩
    exact hnx
  let z : ℕ → Point := fun n ↦ if hn : x ∈ horizontalProjection (K n) o e then
    o + e.symm !₂[x, upperGraphHeight (K n) o e x] else q n
  have hzK (n : ℕ) : z n ∈ K n := by
    dsimp [z]
    split_ifs with hn
    · exact upperGraphHeight_mem (K n) o e hn
    · exact hqK n
  have hzeq : z =ᶠ[atTop]
      fun n ↦ o + e.symm !₂[x, upperGraphHeight (K n) o e x] := by
    filter_upwards [hqproj] with n hn
    simp [z, hn]
  obtain ⟨w, hwL, hd⟩ := exists_points_in_limit_tendsto_dist_zero K L hlim z hzK
  have hsub : Tendsto (fun n ↦ z n - w n) atTop (𝓝 0) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa [dist_eq_norm] using hd
  have hdx : Tendsto (fun n ↦ cx (z n) - cx (w n)) atTop (𝓝 0) := by
    have heval : Continuous (fun v : Point ↦ e v 0) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).comp e.continuous
    rw [show (fun n ↦ cx (z n) - cx (w n)) =
        fun n ↦ e (z n - w n) 0 by
      funext n
      simp [cx]]
    change Tendsto ((fun v : Point ↦ e v 0) ∘ fun n ↦ z n - w n) atTop (𝓝 0)
    simpa only [map_zero, PiLp.zero_apply] using (heval.tendsto 0).comp hsub
  have hdy : Tendsto (fun n ↦ cy (z n) - cy (w n)) atTop (𝓝 0) := by
    have heval : Continuous (fun v : Point ↦ e v 1) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1).comp e.continuous
    rw [show (fun n ↦ cy (z n) - cy (w n)) =
        fun n ↦ e (z n - w n) 1 by
      funext n
      simp [cy]]
    change Tendsto ((fun v : Point ↦ e v 1) ∘ fun n ↦ z n - w n) atTop (𝓝 0)
    simpa only [map_zero, PiLp.zero_apply] using (heval.tendsto 0).comp hsub
  have hcxz : Tendsto (fun n ↦ cx (z n)) atTop (𝓝 x) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hzeq] with n hn
    rw [hn]
    simp [cx]
  have hcxw : Tendsto (fun n ↦ cx (w n)) atTop (𝓝 x) := by
    have h := hcxz.sub hdx
    convert h using 1 <;> simp
  have hgL : Tendsto (fun n ↦ upperGraphHeight L o e (cx (w n))) atTop
      (𝓝 (upperGraphHeight L o e x)) := by
    have hcont : ContinuousAt (upperGraphHeight L o e) x :=
      (locallyLipschitzOn_upperGraphHeight L o e).continuousOn.continuousAt
        (isOpen_Ioo.mem_nhds hx)
    exact hcont.tendsto.comp hcxw
  have hlower : ∀ᶠ n in atTop,
      cy (q n) ≤ upperGraphHeight (K n) o e x := by
    filter_upwards [hqcx] with n hnx
    apply (upperGraphHeight_isGreatest (K n) o e (by
      exact ⟨q n, hqK n, hnx⟩)).2
    change o + e.symm !₂[x, cy (q n)] ∈ K n
    rw [show o + e.symm !₂[x, cy (q n)] = q n by
      calc
        o + e.symm !₂[x, cy (q n)] = o + e.symm !₂[cx (q n), cy (q n)] := by
          rw [hnx]
        _ = q n := reconstruct (q n)]
    exact hqK n
  have hupper : ∀ᶠ n in atTop,
      upperGraphHeight (K n) o e x ≤
        upperGraphHeight L o e (cx (w n)) + (cy (z n) - cy (w n)) := by
    filter_upwards [hzeq] with n hzn
    have hwproj : cx (w n) ∈ horizontalProjection L o e :=
      ⟨w n, hwL n, rfl⟩
    have hwy : cy (w n) ≤ upperGraphHeight L o e (cx (w n)) := by
      apply (upperGraphHeight_isGreatest L o e hwproj).2
      change o + e.symm !₂[cx (w n), cy (w n)] ∈ L
      rw [reconstruct (w n)]
      exact hwL n
    have hzy : cy (z n) = upperGraphHeight (K n) o e x := by
      rw [hzn]
      simp [cy]
    rw [← hzy]
    linarith
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hcyq
    (by simpa using hgL.add hdy) hlower hupper

private theorem eventually_mem_horizontalProjection_of_hausdorffDist
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    {x : ℝ} (hx : x ∈ Set.Ioo (horizontalBounds L o e).1
      (horizontalBounds L o e).2) :
    ∀ᶠ n in atTop, x ∈ horizontalProjection (K n) o e := by
  have hxproj : x ∈ horizontalProjection L o e := by
    rw [horizontalProjection_eq_Icc]
    exact ⟨hx.1.le, hx.2.le⟩
  let p := o + e.symm !₂[x, upperGraphHeight L o e x]
  have hp : p ∈ L := upperGraphHeight_mem L o e hxproj
  have hpcoord : e (p - o) 0 = x := by simp [p]
  have hpint : e (p - o) 0 ∈ Set.Ioo (horizontalBounds L o e).1
      (horizontalBounds L o e).2 := by
    rw [hpcoord]
    exact hx
  obtain ⟨q, hqK, -, hqx⟩ :=
    exists_tendsto_points_with_horizontal_coordinate K L hlim o e hp hpint
  filter_upwards [hqx] with n hn
  exact ⟨q n, hqK n, hn.trans hpcoord⟩

/-- Upper graph surface densities converge almost everywhere on the interior limit projection. -/
theorem ae_tendsto_upperGraphSurfaceIntegrand_of_hausdorffDist
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    {ψ : Real.Angle → ℝ} (hψ : Continuous ψ) :
    ∀ᵐ x : ℝ, x ∈ Set.Ioo (horizontalBounds L o e).1
      (horizontalBounds L o e).2 →
        Tendsto (fun n ↦ upperGraphSurfaceIntegrand (K n) o e ψ x) atTop
          (𝓝 (upperGraphSurfaceIntegrand L o e ψ x)) := by
  have haeK : ∀ᵐ x : ℝ, ∀ n,
      x ∈ Set.Ioo (horizontalBounds (K n) o e).1 (horizontalBounds (K n) o e).2 →
        DifferentiableAt ℝ (upperGraphHeight (K n) o e) x :=
    MeasureTheory.ae_all_iff.mpr fun n ↦ ae_differentiableAt_upperGraphHeight (K n) o e
  have haeL := ae_differentiableAt_upperGraphHeight L o e
  filter_upwards [haeK, haeL] with x hdiffK hdiffL hx
  let left := (horizontalBounds L o e).1
  let right := (horizontalBounds L o e).2
  let a := (left + x) / 2
  let b := (x + right) / 2
  have hax : a < x := by dsimp [a, left]; linarith [hx.1]
  have hxb : x < b := by dsimp [b, right]; linarith [hx.2]
  have haL : a ∈ Set.Ioo (horizontalBounds L o e).1
      (horizontalBounds L o e).2 := by
    dsimp [a, left]
    constructor <;> linarith [hx.1, hx.2]
  have hbL : b ∈ Set.Ioo (horizontalBounds L o e).1
      (horizontalBounds L o e).2 := by
    dsimp [b, right]
    constructor <;> linarith [hx.1, hx.2]
  have haK := eventually_mem_horizontalProjection_of_hausdorffDist K L hlim o e haL
  have hbK := eventually_mem_horizontalProjection_of_hausdorffDist K L hlim o e hbL
  have hconc : ∀ᶠ n in atTop,
      ConcaveOn ℝ (Set.Ioo a b) (upperGraphHeight (K n) o e) := by
    filter_upwards [haK, hbK] with n han hbn
    apply (concaveOn_upperGraphHeight (K n) o e).subset _ (convex_Ioo a b)
    intro y hy
    rw [horizontalProjection_eq_Icc] at han hbn ⊢
    exact ⟨han.1.trans hy.1.le, hy.2.le.trans hbn.2⟩
  have hdiffEventually : ∀ᶠ n in atTop,
      DifferentiableAt ℝ (upperGraphHeight (K n) o e) x := by
    filter_upwards [haK, hbK] with n han hbn
    apply hdiffK n
    rw [horizontalProjection_eq_Icc] at han hbn
    exact ⟨han.1.trans_lt hax, hxb.trans_le hbn.2⟩
  have hpointwise (y : ℝ) (hy : y ∈ Set.Ioo a b) :
      Tendsto (fun n ↦ upperGraphHeight (K n) o e y) atTop
        (𝓝 (upperGraphHeight L o e y)) := by
    apply tendsto_upperGraphHeight_of_hausdorffDist K L hlim o e
    exact ⟨haL.1.trans hy.1, hy.2.trans hbL.2⟩
  have hderiv : Tendsto (fun n ↦ deriv (upperGraphHeight (K n) o e) x) atTop
      (𝓝 (deriv (upperGraphHeight L o e) x)) :=
    ConcaveOn.tendsto_deriv_of_tendsto_Ioo ⟨hax, hxb⟩ hconc hpointwise hdiffEventually
      (hdiffL hx)
  have hdensity := (continuous_surfaceDensity_of_slope e hψ).continuousAt.tendsto.comp hderiv
  change Tendsto ((fun r : ℝ ↦ ψ (vectorNormalAngle (e.symm !₂[-r, 1])) *
    Real.sqrt (1 + r ^ 2)) ∘ fun n ↦ deriv (upperGraphHeight (K n) o e) x)
      atTop (𝓝 (upperGraphSurfaceIntegrand L o e ψ x))
  simpa only [upperGraphSurfaceIntegrand] using hdensity

private theorem tendsto_vectorSupport_of_hausdorffDist
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) {u : Point} (hu : ‖u‖ = 1) :
    Tendsto (fun n ↦ vectorSupport (K n) u) atTop (𝓝 (vectorSupport L u)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ dist_nonneg) _ hlim
  intro n
  simpa only [Real.dist_eq] using
    (compactSet_support_continuity (K n) L (K n).nonempty
      (K n).isCompact L.nonempty L.isCompact).2.1 u hu

private theorem horizontalBounds_snd_eq_vectorSupport (K : ConvexBody Point)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) :
    (horizontalBounds K o e).2 =
      vectorSupport K (e.symm !₂[1, 0]) - inner ℝ o (e.symm !₂[1, 0]) := by
  let u : Point := e.symm !₂[1, 0]
  have hu (p : Point) : e (p - o) 0 = inner ℝ p u - inner ℝ o u := by
    rw [← inner_sub_left, ← e.inner_map_map]
    simp [u, PiLp.inner_apply, Fin.sum_univ_two]
  obtain ⟨p, hp, hsup, hge⟩ := K.isCompact.exists_sSup_image_eq_and_ge K.nonempty
    (show Continuous (fun p : Point ↦ inner ℝ p u) from
      continuous_id.inner continuous_const).continuousOn
  change sSup ((fun p : Point ↦ e (p - o) 0) '' (K : Set Point)) = _
  rw [show vectorSupport K u = inner ℝ p u by exact hsup]
  apply le_antisymm
  · apply csSup_le (K.nonempty.image _)
    rintro _ ⟨q, hq, rfl⟩
    change e (q - o) 0 ≤ inner ℝ p u - inner ℝ o u
    rw [hu q]
    exact sub_le_sub_right (hge q hq) _
  · apply le_csSup
    · have hc : Continuous (fun p : Point ↦ e (p - o)) :=
        e.continuous.comp (continuous_id.sub continuous_const)
      exact K.isCompact.bddAbove_image
        ((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).comp hc).continuousOn
    · exact ⟨p, hp, hu p⟩

private theorem horizontalBounds_fst_eq_vectorSupport (K : ConvexBody Point)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) :
    (horizontalBounds K o e).1 =
      -vectorSupport K (-(e.symm !₂[1, 0])) - inner ℝ o (e.symm !₂[1, 0]) := by
  let u : Point := e.symm !₂[1, 0]
  have hu (p : Point) : e (p - o) 0 = inner ℝ p u - inner ℝ o u := by
    rw [← inner_sub_left, ← e.inner_map_map]
    simp [u, PiLp.inner_apply, Fin.sum_univ_two]
  obtain ⟨p, hp, hsup, hge⟩ := K.isCompact.exists_sSup_image_eq_and_ge K.nonempty
    (show Continuous (fun p : Point ↦ inner ℝ p (-u)) from
      continuous_id.inner continuous_const).continuousOn
  change sInf ((fun p : Point ↦ e (p - o) 0) '' (K : Set Point)) = _
  rw [show vectorSupport K (-u) = inner ℝ p (-u) by exact hsup]
  apply le_antisymm
  · apply csInf_le
    · have hc : Continuous (fun p : Point ↦ e (p - o)) :=
        e.continuous.comp (continuous_id.sub continuous_const)
      exact K.isCompact.bddBelow_image
        ((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).comp hc).continuousOn
    · refine ⟨p, hp, ?_⟩
      change e (p - o) 0 = -inner ℝ p (-u) - inner ℝ o u
      rw [hu p]
      simp
  · apply le_csInf (K.nonempty.image _)
    rintro _ ⟨q, hq, rfl⟩
    change -inner ℝ p (-u) - inner ℝ o u ≤ e (q - o) 0
    rw [hu q]
    have h := hge q hq
    simp only [inner_neg_right] at h ⊢
    linarith

/-- Horizontal projection endpoints converge with their convex bodies. -/
private theorem tendsto_horizontalBounds_of_hausdorffDist
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) :
    Tendsto (fun n ↦ horizontalBounds (K n) o e) atTop
      (𝓝 (horizontalBounds L o e)) := by
  let u : Point := e.symm !₂[1, 0]
  have hu : ‖u‖ = 1 := by
    rw [show ‖u‖ = ‖(!₂[1, 0] : Point)‖ by exact e.symm.norm_map _]
    rw [EuclideanSpace.norm_eq]
    norm_num [Fin.sum_univ_two]
  rw [show (fun n ↦ horizontalBounds (K n) o e) =
      fun n ↦ (-vectorSupport (K n) (-u) - inner ℝ o u,
        vectorSupport (K n) u - inner ℝ o u) by
      funext n
      ext <;> simp [horizontalBounds_fst_eq_vectorSupport,
        horizontalBounds_snd_eq_vectorSupport, u]]
  rw [show horizontalBounds L o e =
      (-vectorSupport L (-u) - inner ℝ o u,
        vectorSupport L u - inner ℝ o u) by
      ext <;> simp [horizontalBounds_fst_eq_vectorSupport,
        horizontalBounds_snd_eq_vectorSupport, u]]
  apply Tendsto.prodMk_nhds
  · exact (tendsto_vectorSupport_of_hausdorffDist K L hlim (by simpa using hu)).neg.sub_const _
  · exact (tendsto_vectorSupport_of_hausdorffDist K L hlim hu).sub_const _

private theorem weightedSurfaceIntegral_eq_upperGraphIntegral
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    (ψ : Real.Angle → ℝ) (hψ : Continuous ψ) {ε : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0) :
    (∫ t, ψ t ∂surfaceAreaMeasure K) =
      ∫ x in Set.Icc (horizontalBounds K o e).1 (horizontalBounds K o e).2,
        upperGraphSurfaceIntegrand K o e ψ x := by
  have hformula := (surfaceAreaMeasure_construction K).2.2.2.2 o e ψ hψ ε hε hsupport
  have hle : (horizontalBounds K o e).1 ≤ (horizontalBounds K o e).2 := by
    obtain ⟨x, hx⟩ := K.nonempty.image (fun p : Point ↦ e (p - o) 0)
    change x ∈ horizontalProjection K o e at hx
    rw [horizontalProjection_eq_Icc] at hx
    exact hx.1.trans hx.2
  rcases hle.lt_or_eq with hlt | heq
  · exact (hformula.1 hlt).2
  · rw [hformula.2 heq, heq]
    simp

/-- Weighted upper-normal surface integrals are continuous under Hausdorff convergence. -/
theorem tendsto_integral_surfaceAreaMeasure_of_hausdorffDist
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    {ψ : Real.Angle → ℝ} (hψ : Continuous ψ) {ε : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0) :
    Tendsto (fun n ↦ ∫ t, ψ t ∂surfaceAreaMeasure (K n)) atTop
      (𝓝 (∫ t, ψ t ∂surfaceAreaMeasure L)) := by
  obtain ⟨t, -, ht⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hψ.norm.continuousOn
  let M := ‖ψ t‖
  have hM (u : Real.Angle) : ‖ψ u‖ ≤ M := ht trivial
  have hM0 : 0 ≤ M := norm_nonneg _
  have hb := tendsto_horizontalBounds_of_hausdorffDist K L hlim o e
  have ha : Tendsto (fun n ↦ (horizontalBounds (K n) o e).1) atTop
      (𝓝 (horizontalBounds L o e).1) := continuousAt_fst.tendsto.comp hb
  have hb' : Tendsto (fun n ↦ (horizontalBounds (K n) o e).2) atTop
      (𝓝 (horizontalBounds L o e).2) := continuousAt_snd.tendsto.comp hb
  have hgraph := tendsto_integral_Icc_of_tendsto_endpoints_of_bound ha hb'
    (Eventually.of_forall fun n ↦
      (integrable_upperGraphSurfaceIntegrand (K n) o e ψ hψ hε hsupport _ _).1)
    (mul_nonneg hM0 (inv_nonneg.mpr hε.le))
    (Eventually.of_forall fun n ↦ Eventually.of_forall fun x _ ↦
      norm_upperGraphSurfaceIntegrand_le (K n) o e ψ hε hsupport hM x)
    (ae_tendsto_upperGraphSurfaceIntegrand_of_hausdorffDist K L hlim o e hψ)
  rw [weightedSurfaceIntegral_eq_upperGraphIntegral L o e ψ hψ hε hsupport]
  apply hgraph.congr'
  filter_upwards [] with n
  exact (weightedSurfaceIntegral_eq_upperGraphIntegral (K n) o e ψ hψ hε hsupport).symm

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Properties
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

private theorem mem_exposedEdge_iff_isExteriorNormal (K : ConvexBody Point)
    {p : Point} (hp : p ∈ K) (t : Real.Angle) :
    p ∈ exposedEdge K t ↔ IsExteriorNormal K p t := by
  constructor
  · intro h q hq
    have he : inner ℝ p (normalVector t) = supportValue K t := h.2
    rw [inner_sub_left, he]
    exact sub_nonpos.mpr (inner_le_supportValue K hq t)
  · intro h
    refine ⟨hp, le_antisymm (inner_le_supportValue K hp t) ?_⟩
    apply csSup_le (K.nonempty.image _)
    rintro _ ⟨q, hq, rfl⟩
    exact sub_nonpos.mp (by simpa only [inner_sub_left] using h q hq)

private theorem mem_exposedEdge_iff_exteriorNormalAngle_eq (K : ConvexBody Point)
    {p : Point} (hp : p ∈ regularBoundary K) (t : Real.Angle) :
    p ∈ exposedEdge K t ↔ exteriorNormalAngle K p = t := by
  have hpK : p ∈ K := by
    change p ∈ (K : Set Point)
    simpa only [K.isCompact.isClosed.closure_eq] using frontier_subset_closure hp.1
  rw [mem_exposedEdge_iff_isExteriorNormal K hpK]
  have hn : IsExteriorNormal K p (exteriorNormalAngle K p) := by
    simp only [exteriorNormalAngle, dite_eq_left hp.2]
    exact hp.2.exists.choose_spec
  exact ⟨fun ht ↦ hp.2.unique hn ht, fun ht ↦ ht ▸ hn⟩

private theorem faceUnion_inter_regularBoundary (K : ConvexBody Point) (E : Set Real.Angle) :
    (⋃ t ∈ E, exposedEdge K t) ∩ regularBoundary K =
      exteriorNormalAngle K ⁻¹' E ∩ regularBoundary K := by
  ext p
  constructor
  · rintro ⟨hp, hreg⟩
    obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hp
    refine ⟨?_, hreg⟩
    change exteriorNormalAngle K p ∈ E
    rwa [(mem_exposedEdge_iff_exteriorNormalAngle_eq K hreg t).mp hp]
  · rintro ⟨hp, hreg⟩
    exact ⟨Set.mem_iUnion₂.mpr ⟨exteriorNormalAngle K p, hp,
      (mem_exposedEdge_iff_exteriorNormalAngle_eq K hreg _).mpr rfl⟩, hreg⟩

private theorem surfaceAreaMeasure_face_union_of_interior_nonempty (K : ConvexBody Point)
    (hK : (interior (K : Set Point)).Nonempty)
    (E : Set Real.Angle) (hE : MeasurableSet E) :
    surfaceAreaMeasure K E = Measure.hausdorffMeasure 1 (⋃ t ∈ E, exposedEdge K t) := by
  simp only [surfaceAreaMeasure,
    ite_eq_right (not_subsingleton_of_interior_nonempty K hK),
    dite_eq_right (not_exists_segmentPresentation_of_interior_nonempty K hK)]
  rw [Measure.map_apply_of_aemeasurable
      (aemeasurable_exteriorNormalAngle_restrict_regularBoundary K _) hE,
    Measure.restrict_apply' (measurableSet_regularBoundary K),
    ← faceUnion_inter_regularBoundary]
  apply measure_congr
  rw [ae_eq_set]
  constructor
  · apply measure_mono_null (fun p hp ↦ (hp.2 hp.1.1).elim) measure_empty
  · apply measure_mono_null ?_ (hausdorffMeasure_irregularBoundary_eq_zero K hK)
    rintro p ⟨hp, hnot⟩
    refine ⟨?_, fun hreg ↦ hnot ⟨hp, hreg⟩⟩
    obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.mp hp
    exact mem_frontier_of_mem_of_isExteriorNormal K hpt.1
      ((mem_exposedEdge_iff_isExteriorNormal K hpt.1 t).mp hpt)

private theorem surfaceAreaMeasure_face_union_of_subsingleton (K : ConvexBody Point)
    (hK : (K : Set Point).Subsingleton) (E : Set Real.Angle) :
    surfaceAreaMeasure K E = Measure.hausdorffMeasure 1 (⋃ t ∈ E, exposedEdge K t) := by
  rw [surfaceAreaMeasure_eq_zero_of_subsingleton K hK]
  change 0 = _
  symm
  let _ := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  obtain ⟨p, hp⟩ := K.nonempty
  apply measure_mono_null (t := {p})
  · intro q hq
    obtain ⟨t, ht, hqt⟩ := Set.mem_iUnion₂.mp hq
    exact hK hqt.1 hp
  · simp

theorem surfaceAreaMeasure_face_union (K : ConvexBody Point) :
    IsFiniteMeasure (surfaceAreaMeasure K) ∧
    ((K : Set Point).Subsingleton → surfaceAreaMeasure K = 0) ∧
    (∀ d, IsSegmentPresentation K d → surfaceAreaMeasure K =
      ENNReal.ofReal (dist d.1 d.2.1) •
        (Measure.dirac d.2.2 + Measure.dirac (d.2.2 + ((Real.pi : ℝ) : Real.Angle)))) ∧
    ((interior (K : Set Point)).Nonempty → surfaceAreaMeasure K =
      Measure.map (exteriorNormalAngle K)
        ((Measure.hausdorffMeasure 1).restrict (regularBoundary K))) ∧
    (∀ E : Set Real.Angle, MeasurableSet E →
      ((interior (K : Set Point)).Nonempty ∨
        ∃ a b : ℝ, a ≤ b ∧ b < a + Real.pi ∧
          E ⊆ (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Icc a b) →
      surfaceAreaMeasure K E =
        Measure.hausdorffMeasure 1 (⋃ t ∈ E, exposedEdge K t)) := by
  obtain ⟨hfinite, hpoint, hsegment, _, _⟩ := surfaceAreaMeasure_construction K
  refine ⟨hfinite, hpoint, hsegment, ?_, ?_⟩
  · intro hK
    simp only [surfaceAreaMeasure,
      ite_eq_right (not_subsingleton_of_interior_nonempty K hK),
      dite_eq_right (not_exists_segmentPresentation_of_interior_nonempty K hK)]
  · intro E hE hdomain
    by_cases hsub : (K : Set Point).Subsingleton
    · exact surfaceAreaMeasure_face_union_of_subsingleton K hsub E
    by_cases hint : (interior (K : Set Point)).Nonempty
    · exact surfaceAreaMeasure_face_union_of_interior_nonempty K hint E hE
    obtain ⟨a, b, hab, hwidth, hsubset⟩ := hdomain.resolve_left hint
    have hseg := exists_segmentPresentation_of_interior_empty K hsub
      (Set.not_nonempty_iff_eq_empty.mp hint)
    obtain ⟨d, hd⟩ := hseg
    exact surfaceAreaMeasure_face_union_of_segmentPresentation K d hd E hE hab hwidth hsubset

instance isFiniteMeasure_surfaceAreaMeasure (K : ConvexBody Point) :
    IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1

/-- A measurable set of normal directions lying in an angular interval of width less than `π`,
on which every face of `K` degenerates to one and the same point, is null for the surface area
measure of `K`. -/
theorem surfaceAreaMeasure_null_of_exposedEdge_subset_singleton (K : ConvexBody Point)
    {E : Set Real.Angle} (hE : MeasurableSet E) {a b : ℝ} (hab : a ≤ b) (hba : b < a + Real.pi)
    (hEab : E ⊆ (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Icc a b) (p : Point)
    (hsub : ∀ t ∈ E, exposedEdge K t ⊆ {p}) :
    surfaceAreaMeasure K E = 0 := by
  let _ := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  rw [(surfaceAreaMeasure_face_union K).2.2.2.2 E hE (Or.inr ⟨a, b, hab, hba, hEab⟩)]
  refine measure_mono_null (t := {p}) ?_ (by simp)
  intro x hx
  obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
  exact hsub t ht hxt

/-- The surface measure of a convex body vanishes on the open angular window strictly between two
normal angles less than a half turn apart at which one and the same point attains the support. -/
theorem surfaceAreaMeasure_angleImage_Ioo_eq_zero_of_mem_exposedEdge (K : ConvexBody Point)
    {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi) {p : Point}
    (hpa : p ∈ exposedEdge K (a : Real.Angle))
    (hpb : p ∈ exposedEdge K (b : Real.Angle)) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b) = 0 := by
  refine surfaceAreaMeasure_null_of_exposedEdge_subset_singleton K
    (Real.Angle.isOpen_image_Ioo a b).measurableSet hab.le hba
    (Set.image_mono Set.Ioo_subset_Icc_self) p fun t ht ↦ ?_
  obtain ⟨s, hs, rfl⟩ := ht
  exact (exposedEdge_eq_singleton_of_mem_exposedEdge_of_mem_Ioo hba hs hpa hpb).subset

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Boundary Extension
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace MovingSofa

/-- Agreement of positive-vertex increments with tangent-coordinate surface integrals extends
from half-open subintervals to every measurable set avoiding the initial endpoint. -/
theorem intervalStieltjesMeasure_eq_surfaceIntegral_of_increment
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ i t, (f i).toFun t =
      (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 i)
    (hinc : ∀ (c d : Set.Icc a b), c < d → ∀ i : Fin 2,
      (edgeVertices K (((d : Set.Icc a b) : ℝ) : Real.Angle)).1 i -
          (edgeVertices K (((c : Set.Icc a b) : ℝ) : Real.Angle)).1 i =
        ∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc (c : ℝ) d,
          tangentVector u i ∂surfaceAreaMeasure K) :
    ∀ (i : Fin 2) (E : Set (Set.Icc a b)), MeasurableSet E →
      (∀ t ∈ E, a < (t : ℝ)) →
      intervalStieltjesMeasure (f i) E =
        ∫ u in (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i ∂surfaceAreaMeasure K := by
  let A := Set.Ioc a b
  let c : A → Real.Angle := fun t ↦ ((t : ℝ) : Real.Angle)
  let j : A → Set.Icc a b := fun t ↦ ⟨t, t.property.1.le, t.property.2⟩
  have hc : MeasurableEmbedding c := by
    refine ⟨?_, (Real.Angle.continuous_coe.comp continuous_subtype_val).measurable, ?_⟩
    · intro x y hxy
      exact Subtype.ext (Real.Angle.injOn_coe_Ioc hturn x.property y.property hxy)
    · intro s hs
      let S : Set ℝ := Subtype.val '' s
      have hS : MeasurableSet S :=
        (MeasurableEmbedding.subtype_coe measurableSet_Ioc).measurableSet_image' hs
      have hSI : Set.InjOn (fun t : ℝ ↦ (t : Real.Angle)) S := by
        intro x hx y hy hxy
        obtain ⟨tx, htx, rfl⟩ := hx
        obtain ⟨ty, hty, rfl⟩ := hy
        exact Real.Angle.injOn_coe_Ioc hturn tx.property ty.property hxy
      have hm := hS.image_of_continuousOn_injOn Real.Angle.continuous_coe.continuousOn hSI
      convert hm using 1
      ext u
      simp [S, c]
  have hj : Measurable j := by fun_prop
  intro i E hE hEa
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) :=
    (surfaceAreaMeasure_face_union K).1
  have hgi : Integrable (fun u : Real.Angle ↦ tangentVector u i) (surfaceAreaMeasure K) := by
    rw [← integrableOn_univ]
    exact ContinuousOn.integrableOn_compact isCompact_univ (by
      fin_cases i
      · exact Real.Angle.continuous_sin.neg.continuousOn
      · exact Real.Angle.continuous_cos.continuousOn)
  obtain ⟨ν, hν⟩ :=
    MeasurableEmbedding.exists_vectorMeasure_image_integral hc (surfaceAreaMeasure K)
      (fun u ↦ tangentVector u i) hgi
  have hmeasure : intervalStieltjesMeasure (f i) = ν.map j := by
    apply MeasureTheory.VectorMeasure.ext_of_Ioc
    · intro x y hxy
      have hpre : j ⁻¹' Ioc x y = {t : A | (x : ℝ) < (t : ℝ) ∧ (t : ℝ) ≤ (y : ℝ)} := rfl
      have hpremeas : MeasurableSet (j ⁻¹' Ioc x y) :=
        measurableSet_Ioc.preimage hj
      have himage : c '' (j ⁻¹' Ioc x y) =
          (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc (x : ℝ) y := by
        ext u
        constructor
        · rintro ⟨t, ht, rfl⟩
          exact ⟨t, ht, rfl⟩
        · rintro ⟨t, ht, rfl⟩
          exact ⟨⟨t, x.property.1.trans_lt ht.1, ht.2.trans y.property.2⟩, ht, rfl⟩
      rw [intervalStieltjesMeasure_Ioc (f i) x y hxy.le,
        VectorMeasure.map_apply _ hj measurableSet_Ioc, hν _ hpremeas, himage,
        hf i y, hf i x, hinc x y hxy i]
    · let aa : Set.Icc a b := ⟨a, le_rfl, hab.le⟩
      let bb : Set.Icc a b := ⟨b, hab.le, le_rfl⟩
      have hpre : j ⁻¹' univ = univ := preimage_univ
      have hunivmeas : MeasurableSet (univ : Set A) := MeasurableSet.univ
      have himage : c '' (univ : Set A) =
          (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc a b := by
        ext u
        simp [c, A]
      have hzero : intervalStieltjesMeasure (f i) {aa} = 0 := by
        rw [intervalStieltjesMeasure, (f i).boundedVariation.vectorMeasure_singleton,
          (f i).right_continuous aa |>.rightLim_eq]
        have hbot : 𝓝[<] aa = ⊥ := by
          have hIio : Iio aa = ∅ := by
            ext t
            simp only [mem_Iio, mem_empty_iff_false, iff_false]
            exact not_lt_of_ge t.property.1
          rw [hIio]
          exact nhdsWithin_empty aa
        rw [leftLim_eq_of_eq_bot _ hbot, sub_self]
      have hsplit : (univ : Set (Set.Icc a b)) = Ioc aa bb ∪ {aa} := by
        ext t
        simp only [mem_univ, true_iff, mem_union, mem_Ioc, mem_singleton_iff]
        by_cases hta : aa = t
        · exact Or.inr hta.symm
        · exact Or.inl ⟨lt_of_le_of_ne t.property.1 hta, t.property.2⟩
      have hlhs : intervalStieltjesMeasure (f i) univ =
          intervalStieltjesMeasure (f i) (Ioc aa bb) := by
        rw [hsplit, VectorMeasure.of_union (disjoint_singleton_right.2 (by simp))
          measurableSet_Ioc (measurableSet_singleton aa),
          hzero, add_zero]
      rw [hlhs, intervalStieltjesMeasure_Ioc (f i) aa bb hab.le,
        VectorMeasure.map_apply _ hj MeasurableSet.univ, hpre, hν _ hunivmeas, himage,
        hf i bb, hf i aa, hinc aa bb hab i]
  have himageE : c '' (j ⁻¹' E) =
      (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨j t, ht, rfl⟩
    · rintro ⟨t, htE, rfl⟩
      exact ⟨⟨t, hEa t htE, t.property.2⟩, htE, rfl⟩
  rw [hmeasure, VectorMeasure.map_apply _ hj hE, hν _ (hE.preimage hj), himageE]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Opposite
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- The opposite-angle surface measure and support function. -/
@[expose]
def oppositeSurfaceData (K : ConvexBody Point) :
    Measure Real.Angle × (Real.Angle → ℝ) :=
  (Measure.map (fun t ↦ t - ((Real.pi : ℝ) : Real.Angle)) (surfaceAreaMeasure K),
    fun t ↦ supportValue K (t + ((Real.pi : ℝ) : Real.Angle)))

/-- The opposite surface measure is the half-turn translate of the surface measure. -/
theorem oppositeSurfaceData_fst (K : ConvexBody Point) :
    (oppositeSurfaceData K).1 =
      Measure.map (fun t : Real.Angle ↦ t - ((Real.pi : ℝ) : Real.Angle))
        (surfaceAreaMeasure K) := rfl

instance isFiniteMeasure_oppositeSurfaceData (K : ConvexBody Point) :
    IsFiniteMeasure (oppositeSurfaceData K).1 := by
  rw [oppositeSurfaceData_fst]
  exact Measure.isFiniteMeasure_map _ _

/-- The opposite support function of a convex body is continuous in the normal direction. -/
theorem continuous_oppositeSurfaceData_snd (K : ConvexBody Point) :
    Continuous (oppositeSurfaceData K).2 :=
  (continuous_supportValue K).comp (continuous_id.add continuous_const)

/-- Integrating a `π`-shifted integrand against the opposite surface measure over an open angular
window is integrating the integrand itself against the surface-area measure over the `π`-translated
window.  The endpoints of the translated window are given as hypotheses so that call sites may
normalize them arithmetically. -/
theorem setIntegral_oppositeSurfaceData_angleImage_Ioo (K : ConvexBody Point) {a b a' b' : ℝ}
    (ha : a' = a + Real.pi) (hb : b' = b + Real.pi) {f : Real.Angle → ℝ} (hf : Measurable f) :
    (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        f (t + ((Real.pi : ℝ) : Real.Angle)) ∂(oppositeSurfaceData K).1) =
      ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a' b',
        f t ∂surfaceAreaMeasure K := by
  subst ha hb
  have hshift : Measurable fun t : Real.Angle ↦ t - ((Real.pi : ℝ) : Real.Angle) :=
    (continuous_id.sub continuous_const).measurable
  have hfshift : Measurable fun t : Real.Angle ↦ f (t + ((Real.pi : ℝ) : Real.Angle)) :=
    hf.comp (continuous_id.add continuous_const).measurable
  have hE : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b) :=
    (Real.Angle.isOpen_image_Ioo a b).measurableSet
  rw [oppositeSurfaceData_fst, setIntegral_map hE hfshift.aestronglyMeasurable hshift.aemeasurable,
    Real.Angle.preimage_sub_pi_image_Ioo]
  simp only [sub_add_cancel]

/-- The opposite surface measure vanishes on an open angular window whose half-turn translate
carries a single support point. -/
theorem oppositeSurfaceData_angleImage_Ioo_eq_zero_of_mem_exposedEdge (K : ConvexBody Point)
    {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi) {p : Point}
    (hpa : p ∈ exposedEdge K ((a + Real.pi : ℝ) : Real.Angle))
    (hpb : p ∈ exposedEdge K ((b + Real.pi : ℝ) : Real.Angle)) :
    (oppositeSurfaceData K).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b) = 0 := by
  have hshift : Measurable fun t : Real.Angle ↦ t - ((Real.pi : ℝ) : Real.Angle) :=
    (continuous_id.sub continuous_const).measurable
  rw [oppositeSurfaceData_fst,
    Measure.map_apply hshift (Real.Angle.isOpen_image_Ioo a b).measurableSet,
    Real.Angle.preimage_sub_pi_image_Ioo]
  exact surfaceAreaMeasure_angleImage_Ioo_eq_zero_of_mem_exposedEdge K (by linarith) (by linarith)
    hpa hpb

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Weak Convergence
-/

public section

noncomputable section

open scoped BigOperators
open Filter MeasureTheory
open scoped Topology

namespace MovingSofa

private def normalCoordinateFrames : Fin 4 → Point ≃ₗᵢ[ℝ] Point :=
  ![LinearIsometryEquiv.refl ℝ Point, LinearIsometryEquiv.neg ℝ,
    coordinateSwap, coordinateSwap.trans (LinearIsometryEquiv.neg ℝ)]

private theorem exists_normalCoordinateFrame (t : Real.Angle) :
    ∃ i, (1 / 2 : ℝ) < normalCoordinateFrames i (normalVector t) 1 := by
  by_contra h
  push Not at h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp [normalCoordinateFrames, coordinateSwap, normalVector, frame] at h0 h1 h2 h3
  have hs : t.sin ^ 2 ≤ 1 / 4 := by nlinarith
  have hc : t.cos ^ 2 ≤ 1 / 4 := by nlinarith
  nlinarith [t.cos_sq_add_sin_sq]

/-- Four coordinate half-circles admit a continuous partition of unity supported
where the upward component of the normal is at least one half. -/
theorem exists_normalCoordinate_partition :
    ∃ (e : Fin 4 → Point ≃ₗᵢ[ℝ] Point) (χ : Fin 4 → Real.Angle → ℝ),
      (∀ i, Continuous (χ i)) ∧ (∀ t, ∑ i, χ i t = 1) ∧
        (∀ i t, e i (normalVector t) 1 < 1 / 2 → χ i t = 0) := by
  let ρ : Fin 4 → Real.Angle → ℝ := fun i t ↦
    max 0 (normalCoordinateFrames i (normalVector t) 1 - 1 / 2)
  have hρ : ∀ i, Continuous (ρ i) := by
    intro i
    dsimp [ρ]
    exact continuous_const.max
      (((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1).comp
        ((normalCoordinateFrames i).continuous.comp continuous_normalVector_angle)).sub
          continuous_const)
  have hpos (t : Real.Angle) : 0 < ∑ i, ρ i t := by
    obtain ⟨i, hi⟩ := exists_normalCoordinateFrame t
    apply Finset.sum_pos' (fun j _ ↦ le_max_left _ _)
    refine ⟨i, Finset.mem_univ _, ?_⟩
    exact (sub_pos.mpr hi).trans_le (le_max_right _ _)
  refine ⟨normalCoordinateFrames, fun i t ↦ ρ i t / ∑ j, ρ j t, ?_, ?_, ?_⟩
  · intro i
    exact (hρ i).div (continuous_finsetSum _ fun j _ ↦ hρ j)
      (fun t ↦ (hpos t).ne')
  · intro t
    rw [← Finset.sum_div]
    exact div_self (hpos t).ne'
  · intro i t ht
    have hz : ρ i t = 0 := max_eq_left (sub_nonpos.mpr ht.le)
    dsimp only
    rw [hz, zero_div]

/-- Convergence for test functions supported in upward normal patches implies
convergence for all continuous test functions. -/
theorem tendsto_surfaceIntegral_of_normal_patches
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hpatch : ∀ (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ), Continuous ψ →
      (∀ t, e (normalVector t) 1 < 1 / 2 → ψ t = 0) →
      Tendsto (fun n ↦ ∫ t, ψ t ∂surfaceAreaMeasure (K n)) atTop
        (𝓝 (∫ t, ψ t ∂surfaceAreaMeasure L)))
    (φ : Real.Angle → ℝ) (hφ : Continuous φ) :
    Tendsto (fun n ↦ ∫ t, φ t ∂surfaceAreaMeasure (K n)) atTop
      (𝓝 (∫ t, φ t ∂surfaceAreaMeasure L)) := by
  obtain ⟨e, χ, hχ, hsum, hsupp⟩ := exists_normalCoordinate_partition
  let ψ : Fin 4 → Real.Angle → ℝ := fun i t ↦ φ t * χ i t
  have hψ (i : Fin 4) : Continuous (ψ i) := hφ.mul (hχ i)
  have hψsum (t : Real.Angle) : ∑ i, ψ i t = φ t := by
    simp only [ψ, ← Finset.mul_sum, hsum, mul_one]
  have hint (C : ConvexBody Point) :
      ∑ i, (∫ t, ψ i t ∂surfaceAreaMeasure C) = ∫ t, φ t ∂surfaceAreaMeasure C := by
    let _ := (surfaceAreaMeasure_construction C).1
    rw [← integral_finsetSum]
    · simp only [hψsum]
    · intro i _
      exact integrableOn_univ.mp ((hψ i).continuousOn.integrableOn_compact isCompact_univ)
  have ht (i : Fin 4) := hpatch (e i) (ψ i) (hψ i) (by
    intro t ht
    simp only [ψ, hsupp i t ht, mul_zero])
  have h := tendsto_finsetSum Finset.univ (fun i _ ↦ ht i)
  simpa only [hint] using h

theorem surfaceAreaMeasure_weak_continuity (K : ℕ → ConvexBody Point)
    (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point) (L : Set Point))
      atTop (𝓝 0)) (φ : Real.Angle → ℝ) (hφ : Continuous φ) :
    Tendsto (fun n ↦ ∫ u, φ u ∂surfaceAreaMeasure (K n))
      atTop (𝓝 (∫ u, φ u ∂surfaceAreaMeasure L)) := by
  apply tendsto_surfaceIntegral_of_normal_patches K L _ φ hφ
  intro e ψ hψ hsupp
  exact tendsto_integral_surfaceAreaMeasure_of_hausdorffDist K L hlim 0 e hψ
    (by norm_num : (0 : ℝ) < 1 / 2) hsupp

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Atom Limits
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- An upper bound by a moving surface atom passes to a Hausdorff limit. -/
theorem le_surfaceAreaMeasure_atom_of_tendsto {K : ℕ → ConvexBody Point}
    {L : ConvexBody Point}
    (hK : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point) (L : Set Point))
      atTop (𝓝 0)) {u : Real.Angle} {x : ℕ → ℝ} {a : ℝ}
    (hx : Tendsto x atTop (𝓝 a))
    (hle : ∀ n, x n ≤ (surfaceAreaMeasure (K n) {u}).toReal) :
    a ≤ (surfaceAreaMeasure L {u}).toReal := by
  let μs : ℕ → FiniteMeasure Real.Angle := fun n ↦
    ⟨surfaceAreaMeasure (K n), (surfaceAreaMeasure_face_union (K n)).1⟩
  let μ : FiniteMeasure Real.Angle :=
    ⟨surfaceAreaMeasure L, (surfaceAreaMeasure_face_union L).1⟩
  have hμ : Tendsto μs atTop (𝓝 μ) := by
    apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro f
    exact surfaceAreaMeasure_weak_continuity K L hK f f.continuous
  have hclosed :
      Filter.limsup (fun n ↦ surfaceAreaMeasure (K n) {u}) atTop ≤
        surfaceAreaMeasure L {u} := by
    have h := FiniteMeasure.limsup_measure_closed_le_of_tendsto hμ
      (isClosed_singleton : IsClosed {u})
    change Filter.limsup (fun n ↦ surfaceAreaMeasure (K n) {u}) atTop ≤
      surfaceAreaMeasure L {u} at h
    exact h
  have hpoint : ∀ n, ENNReal.ofReal (x n) ≤ surfaceAreaMeasure (K n) {u} := by
    intro n
    exact ENNReal.ofReal_le_of_le_toReal (hle n)
  have hlimsup :
      Filter.limsup (fun n ↦ ENNReal.ofReal (x n)) atTop ≤
        Filter.limsup (fun n ↦ surfaceAreaMeasure (K n) {u}) atTop :=
    Filter.limsup_le_limsup (Eventually.of_forall hpoint)
  have hmain : ENNReal.ofReal a ≤ surfaceAreaMeasure L {u} := by
    calc
      ENNReal.ofReal a = Filter.limsup (fun n ↦ ENNReal.ofReal (x n)) atTop :=
        (ENNReal.tendsto_ofReal hx).limsup_eq.symm
      _ ≤ Filter.limsup (fun n ↦ surfaceAreaMeasure (K n) {u}) atTop := hlimsup
      _ ≤ surfaceAreaMeasure L {u} := hclosed
  let _ : IsFiniteMeasure (surfaceAreaMeasure L) := (surfaceAreaMeasure_face_union L).1
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hmain

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Weighted Boundary
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- On a half-open parameter interval of at most one turn, the angular projection is a
measurable embedding. -/
theorem measurableEmbedding_angleCoe_Ioc {a b : ℝ} (hturn : b ≤ a + 2 * Real.pi) :
    MeasurableEmbedding fun t : Ioc a b ↦ ((t : ℝ) : Real.Angle) := by
  refine ⟨?_, (Real.Angle.continuous_coe.comp continuous_subtype_val).measurable, ?_⟩
  · intro x y hxy
    exact Subtype.ext (Real.Angle.injOn_coe_Ioc hturn x.property y.property hxy)
  · intro s hs
    let S : Set ℝ := Subtype.val '' s
    have hS : MeasurableSet S :=
      (MeasurableEmbedding.subtype_coe measurableSet_Ioc).measurableSet_image' hs
    have hSI : Set.InjOn (fun t : ℝ ↦ (t : Real.Angle)) S := by
      intro x hx y hy hxy
      obtain ⟨tx, htx, rfl⟩ := hx
      obtain ⟨ty, hty, rfl⟩ := hy
      exact Real.Angle.injOn_coe_Ioc hturn tx.property ty.property hxy
    have hm := hS.image_of_continuousOn_injOn Real.Angle.continuous_coe.continuousOn hSI
    convert hm using 1
    ext u
    simp [S]

/-- A bounded measurable function on a half-open parameter interval of at most one full turn
extends to a bounded measurable function of the angle. -/
theorem exists_bounded_measurable_angle_extension {a b : ℝ} (hturn : b ≤ a + 2 * Real.pi)
    (ψ : Ioc a b → ℝ) (hψm : Measurable ψ) (C : ℝ) (hC : 0 ≤ C) (hψb : ∀ t, ‖ψ t‖ ≤ C) :
    ∃ Q : Real.Angle → ℝ, Measurable Q ∧ (∀ u, ‖Q u‖ ≤ C) ∧
      ∀ t : Ioc a b, Q ((t : ℝ) : Real.Angle) = ψ t := by
  have hc : MeasurableEmbedding fun t : Ioc a b ↦ ((t : ℝ) : Real.Angle) :=
    measurableEmbedding_angleCoe_Ioc hturn
  refine ⟨Function.extend (fun t : Ioc a b ↦ ((t : ℝ) : Real.Angle)) ψ (fun _ ↦ 0),
    hc.measurable_extend hψm measurable_const, fun u ↦ ?_,
    fun t ↦ hc.injective.extend_apply ψ _ t⟩
  by_cases hu : ∃ t : Ioc a b, ((t : ℝ) : Real.Angle) = u
  · obtain ⟨t, rfl⟩ := hu
    rw [hc.injective.extend_apply]
    exact hψb t
  · rw [Function.extend_apply' _ _ _ hu]
    simpa using hC

/-- A bounded measurable angular weight may be transported through the positive-vertex
Stieltjes identity, coordinate by coordinate. -/
theorem intervalStieltjesIntegral_positiveVertex_coordinate_of_measurable
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ (i : Fin 2) (E : Set (Icc a b)), MeasurableSet E →
      (∀ t ∈ E, a < (t : ℝ)) →
      intervalStieltjesMeasure (f i) E =
        ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i ∂surfaceAreaMeasure K)
    (i : Fin 2) (Q : Real.Angle → ℝ) (C : ℝ)
    (hQm : Measurable fun t : Ioc a b ↦ Q (((t : ℝ) : Real.Angle)))
    (hQb : ∀ u, ‖Q u‖ ≤ C)
    (E : Set (Icc a b)) (hE : MeasurableSet E) (hEa : ∀ t ∈ E, a < (t : ℝ)) :
    intervalStieltjesIntegral (f i)
        (fun t ↦ Q (((t : ℝ) : Real.Angle))) E =
      ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
        Q u * tangentVector u i ∂surfaceAreaMeasure K := by
  let A := Ioc a b
  let c : A → Real.Angle := fun t ↦ ((t : ℝ) : Real.Angle)
  let j : A → Icc a b := fun t ↦ ⟨t, t.property.1.le, t.property.2⟩
  have hc : MeasurableEmbedding c := measurableEmbedding_angleCoe_Ioc hturn
  have hj : MeasurableEmbedding j := by
    refine ⟨fun x y h ↦ Subtype.ext (congrArg (fun z : Icc a b ↦ (z : ℝ)) h), ?_, ?_⟩
    · fun_prop
    · intro s hs
      have hsval : MeasurableSet ((Subtype.val : A → ℝ) '' s) :=
        (MeasurableEmbedding.subtype_coe measurableSet_Ioc).measurableSet_image' hs
      have hsj : j '' s = {t : Icc a b | (t : ℝ) ∈ (Subtype.val : A → ℝ) '' s} := by
        ext t
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x, hx, rfl⟩
        · rintro ⟨x, hx, hxt⟩
          exact ⟨x, hx, Subtype.ext hxt⟩
      rw [hsj]
      exact hsval.preimage measurable_subtype_coe
  let μA := (surfaceAreaMeasure K).comap c
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  let _ : IsFiniteMeasure μA :=
    ⟨by
      rw [hc.comap_apply]
      exact measure_lt_top _ _⟩
  have htancont : Continuous (fun t : A ↦ tangentVector (c t) i) :=
    (continuous_tangentVector_coordinate i).comp
      (Real.Angle.continuous_coe.comp continuous_subtype_val)
  have htan : Integrable (fun t : A ↦ tangentVector (c t) i) μA :=
    Integrable.of_bound htancont.aestronglyMeasurable 1
      (ae_of_all _ fun t ↦ norm_tangentVector_coordinate_le_one (c t) i)
  let ν : SignedMeasure A := μA.withDensityᵥ (fun t ↦ tangentVector (c t) i)
  have hν (S : Set A) (hS : MeasurableSet S) :
      ν S = ∫ u in c '' S, tangentVector u i ∂surfaceAreaMeasure K := by
    rw [show ν S = ∫ t in S, tangentVector (c t) i ∂μA by
      exact withDensityᵥ_apply htan hS]
    have hm := hc.setIntegral_map (μ := μA) (fun u ↦ tangentVector u i) (c '' S)
    rw [hc.map_comap, hc.injective.preimage_image,
      Measure.restrict_restrict_of_subset (image_subset_range c S)] at hm
    exact hm.symm
  have hmeasure : intervalStieltjesMeasure (f i) = ν.map j := by
    apply MeasureTheory.VectorMeasure.ext_of_Ioc
    · intro x y hxy
      have hpremeas : MeasurableSet (j ⁻¹' Ioc x y) :=
        measurableSet_Ioc.preimage hj.measurable
      have himage : c '' (j ⁻¹' Ioc x y) =
          (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' Ioc x y := by
        ext u
        constructor
        · rintro ⟨t, ht, rfl⟩
          exact ⟨j t, ht, rfl⟩
        · rintro ⟨t, ht, rfl⟩
          exact ⟨⟨t, x.property.1.trans_lt ht.1, t.property.2⟩, ht, rfl⟩
      rw [VectorMeasure.map_apply _ hj.measurable measurableSet_Ioc, hν _ hpremeas,
        himage, hf i (Ioc x y) measurableSet_Ioc]
      intro t ht
      exact x.property.1.trans_lt ht.1
    · let aa : Icc a b := ⟨a, le_rfl, hab.le⟩
      let bb : Icc a b := ⟨b, hab.le, le_rfl⟩
      have hzero : intervalStieltjesMeasure (f i) {aa} = 0 := by
        rw [intervalStieltjesMeasure, (f i).boundedVariation.vectorMeasure_singleton,
          (f i).right_continuous aa |>.rightLim_eq]
        have hbot : 𝓝[<] aa = ⊥ := by
          have hIio : Iio aa = ∅ := by
            ext t
            simp only [mem_Iio, mem_empty_iff_false, iff_false]
            exact not_lt_of_ge t.property.1
          rw [hIio]
          exact nhdsWithin_empty aa
        rw [leftLim_eq_of_eq_bot _ hbot, sub_self]
      have hsplit : (univ : Set (Icc a b)) = Ioc aa bb ∪ {aa} := by
        ext t
        simp only [mem_univ, true_iff, mem_union, mem_Ioc, mem_singleton_iff]
        by_cases hta : aa = t
        · exact Or.inr hta.symm
        · exact Or.inl ⟨lt_of_le_of_ne t.property.1 hta, t.property.2⟩
      have hlhs : intervalStieltjesMeasure (f i) univ =
          intervalStieltjesMeasure (f i) (Ioc aa bb) := by
        rw [hsplit, VectorMeasure.of_union (disjoint_singleton_right.2 (by simp))
          measurableSet_Ioc (measurableSet_singleton aa), hzero, add_zero]
      have himage : c '' (univ : Set A) =
          (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' Ioc aa bb := by
        ext u
        constructor
        · rintro ⟨t, -, rfl⟩
          exact ⟨j t, t.property, rfl⟩
        · rintro ⟨t, ht, rfl⟩
          exact ⟨⟨t, ht⟩, mem_univ _, rfl⟩
      rw [hlhs, VectorMeasure.map_apply _ hj.measurable MeasurableSet.univ,
        preimage_univ, hν _ MeasurableSet.univ, himage,
        hf i (Ioc aa bb) measurableSet_Ioc]
      intro t ht
      exact ht.1
  unfold intervalStieltjesIntegral
  rw [hmeasure, hj.setIntegral_map_vectorMeasure hE]
  change (∫ᵛ t in j ⁻¹' E, Q (c t)
      ∂[ContinuousLinearMap.mul ℝ ℝ; μA.withDensityᵥ fun t ↦ tangentVector (c t) i]) = _
  rw [VectorMeasure.setIntegral_withDensity_mul_of_bounded (q := fun t : A ↦ Q (c t)) htan
    hQm.aestronglyMeasurable C (fun t ↦ hQb (c t))
    (j ⁻¹' E) (hE.preimage hj.measurable)]
  have hm := hc.setIntegral_map (μ := μA)
    (fun u ↦ Q u * tangentVector u i) (c '' (j ⁻¹' E))
  rw [hc.map_comap, hc.injective.preimage_image,
    Measure.restrict_restrict_of_subset (image_subset_range c (j ⁻¹' E))] at hm
  have himageE : c '' (j ⁻¹' E) =
      (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨j t, ht, rfl⟩
    · rintro ⟨t, htE, rfl⟩
      exact ⟨⟨t, hEa t htE, t.property.2⟩, htE, rfl⟩
  rw [← himageE]
  exact hm.symm

/-- A continuous angular weight may be transported through the positive-vertex Stieltjes
identity, coordinate by coordinate. -/
theorem intervalStieltjesIntegral_positiveVertex_coordinate
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ (i : Fin 2) (E : Set (Icc a b)), MeasurableSet E →
      (∀ t ∈ E, a < (t : ℝ)) →
      intervalStieltjesMeasure (f i) E =
        ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i ∂surfaceAreaMeasure K)
    (i : Fin 2) (Q : Real.Angle → ℝ) (hQ : Continuous Q)
    (E : Set (Icc a b)) (hE : MeasurableSet E) (hEa : ∀ t ∈ E, a < (t : ℝ)) :
    intervalStieltjesIntegral (f i)
        (fun t ↦ Q (((t : ℝ) : Real.Angle))) E =
      ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
        Q u * tangentVector u i ∂surfaceAreaMeasure K :=
  intervalStieltjesIntegral_positiveVertex_coordinate_of_measurable K hab hturn f hf i Q
    ‖ContinuousMap.equivBoundedOfCompact Real.Angle ℝ ⟨Q, hQ⟩‖
    (hQ.comp (Real.Angle.continuous_coe.comp continuous_subtype_val)).measurable
    (fun u ↦ BoundedContinuousFunction.norm_coe_le_norm
      (ContinuousMap.equivBoundedOfCompact Real.Angle ℝ ⟨Q, hQ⟩) u) E hE hEa

/-- A bounded measurable angular weight times a frame tangent coordinate is integrable against
the surface measure on every measurable set of angles represented in the half-open parameter
interval. -/
theorem integrableOn_mul_tangentVector_of_bounded
    (K : ConvexBody Point) {a b : ℝ} (hturn : b ≤ a + 2 * Real.pi)
    (i : Fin 2) (Q : Real.Angle → ℝ) (C : ℝ)
    (hQm : Measurable fun t : Ioc a b ↦ Q (((t : ℝ) : Real.Angle)))
    (hQb : ∀ u, ‖Q u‖ ≤ C)
    (S : Set Real.Angle) (hS : MeasurableSet S)
    (hSsub : S ⊆ Set.range fun t : Ioc a b ↦ ((t : ℝ) : Real.Angle)) :
    IntegrableOn (fun u ↦ Q u * tangentVector u i) S (surfaceAreaMeasure K) := by
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hC : 0 ≤ C := le_trans (norm_nonneg (Q 0)) (hQb 0)
  obtain ⟨Q', hQ'meas, hQ'b, hQ'eq⟩ := exists_bounded_measurable_angle_extension hturn
    (fun t : Ioc a b ↦ Q (((t : ℝ) : Real.Angle))) hQm C hC (fun t ↦ hQb _)
  have hglobal : Integrable (fun u ↦ Q' u * tangentVector u i) (surfaceAreaMeasure K) := by
    refine Integrable.of_bound
      (hQ'meas.mul (continuous_tangentVector_coordinate i).measurable).aestronglyMeasurable C
      (ae_of_all _ fun u ↦ ?_)
    calc ‖Q' u * tangentVector u i‖ = ‖Q' u‖ * ‖tangentVector u i‖ := norm_mul _ _
      _ ≤ C * 1 :=
        mul_le_mul (hQ'b u) (norm_tangentVector_coordinate_le_one u i) (norm_nonneg _) hC
      _ = C := mul_one C
  refine hglobal.integrableOn.congr_fun (fun u hu ↦ ?_) hS
  obtain ⟨t, rfl⟩ := hSsub hu
  simp only [hQ'eq t]

/-- Pairing the positive-vertex Stieltjes measures with a bounded measurable planar weight is the
surface integral of the pointwise contraction of that weight with the tangent frame. -/
theorem sum_intervalStieltjesIntegral_positiveVertex_dot
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ (i : Fin 2) (E : Set (Icc a b)), MeasurableSet E →
      (∀ t ∈ E, a < (t : ℝ)) →
      intervalStieltjesMeasure (f i) E =
        ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i ∂surfaceAreaMeasure K)
    (φ : Fin 2 → Icc a b → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hφm : ∀ i, Measurable (φ i)) (hφb : ∀ i t, ‖φ i t‖ ≤ C)
    (g : Real.Angle → ℝ)
    (hg : ∀ t : Icc a b, a < (t : ℝ) →
      ∑ i : Fin 2, φ i t * tangentVector (((t : ℝ) : Real.Angle)) i =
        g (((t : ℝ) : Real.Angle)))
    (E : Set (Icc a b)) (hE : MeasurableSet E) (hEa : ∀ t ∈ E, a < (t : ℝ)) :
    (∑ i : Fin 2, intervalStieltjesIntegral (f i) (φ i) E) =
      ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E, g u ∂surfaceAreaMeasure K := by
  set incl : Ioc a b → Icc a b := fun t ↦ ⟨(t : ℝ), t.property.1.le, t.property.2⟩
  have hinclm : Measurable incl := (Continuous.subtype_mk continuous_subtype_val _).measurable
  have himg : (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E =
      (fun t : Ioc a b ↦ ((t : ℝ) : Real.Angle)) '' (incl ⁻¹' E) := by
    ext u
    constructor
    · rintro ⟨t, htE, rfl⟩
      exact ⟨⟨(t : ℝ), hEa t htE, t.property.2⟩, htE, rfl⟩
    · rintro ⟨t, htE, rfl⟩
      exact ⟨incl t, htE, rfl⟩
  have hEmeas : MeasurableSet ((fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E) := by
    rw [himg]
    exact (measurableEmbedding_angleCoe_Ioc hturn).measurableSet_image' (hE.preimage hinclm)
  have hsub : (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E ⊆
      Set.range fun t : Ioc a b ↦ ((t : ℝ) : Real.Angle) := by
    rintro u ⟨t, htE, rfl⟩
    exact ⟨⟨(t : ℝ), hEa t htE, t.property.2⟩, rfl⟩
  choose Q hQm hQb hQeq using fun i : Fin 2 ↦ exists_bounded_measurable_angle_extension hturn
    (fun t : Ioc a b ↦ φ i (incl t)) ((hφm i).comp hinclm) C hC fun t ↦ hφb i (incl t)
  have hQmIoc (i : Fin 2) : Measurable fun t : Ioc a b ↦ Q i (((t : ℝ) : Real.Angle)) :=
    (hQm i).comp (Real.Angle.continuous_coe.comp continuous_subtype_val).measurable
  have hQφ (i : Fin 2) (t : Icc a b) (ht : a < (t : ℝ)) :
      Q i (((t : ℝ) : Real.Angle)) = φ i t := hQeq i ⟨(t : ℝ), ht, t.property.2⟩
  have hterm (i : Fin 2) : intervalStieltjesIntegral (f i) (φ i) E =
      ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
        Q i u * tangentVector u i ∂surfaceAreaMeasure K := by
    rw [show intervalStieltjesIntegral (f i) (φ i) E =
        intervalStieltjesIntegral (f i) (fun t ↦ Q i (((t : ℝ) : Real.Angle))) E from
      VectorMeasure.setIntegral_congr_fun fun t htE ↦ (hQφ i t (hEa t htE)).symm]
    exact intervalStieltjesIntegral_positiveVertex_coordinate_of_measurable K hab hturn f hf i
      (Q i) C (hQmIoc i) (hQb i) E hE hEa
  have hint (i : Fin 2) : IntegrableOn (fun u ↦ Q i u * tangentVector u i)
      ((fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E) (surfaceAreaMeasure K) :=
    integrableOn_mul_tangentVector_of_bounded K hturn i (Q i) C (hQmIoc i) (hQb i) _ hEmeas hsub
  rw [Fin.sum_univ_two, hterm 0, hterm 1, ← integral_add (hint 0) (hint 1)]
  refine setIntegral_congr_fun hEmeas ?_
  rintro u ⟨t, htE, rfl⟩
  have ht := hEa t htE
  simpa only [hQφ 0 t ht, hQφ 1 t ht, Fin.sum_univ_two] using hg t ht

/-- Pairing the positive-vertex Stieltjes measure with the tangent frame gives surface mass. -/
theorem sum_intervalStieltjesIntegral_positiveVertex_tangent
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ (i : Fin 2) (E : Set (Icc a b)), MeasurableSet E →
      (∀ t ∈ E, a < (t : ℝ)) →
      intervalStieltjesMeasure (f i) E =
        ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i ∂surfaceAreaMeasure K)
    (E : Set (Icc a b)) (hE : MeasurableSet E) (hEa : ∀ t ∈ E, a < (t : ℝ)) :
    (∑ i : Fin 2, intervalStieltjesIntegral (f i)
      (fun t ↦ tangentVector (((t : ℝ) : Real.Angle)) i) E) =
      (surfaceAreaMeasure K
        ((fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E)).toReal := by
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hcoord (i : Fin 2) :
      intervalStieltjesIntegral (f i)
          (fun t ↦ tangentVector (((t : ℝ) : Real.Angle)) i) E =
        ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i * tangentVector u i ∂surfaceAreaMeasure K := by
    have hQi : Continuous (fun u : Real.Angle ↦ tangentVector u i) := by
      fin_cases i
      · exact Real.Angle.continuous_sin.neg
      · exact Real.Angle.continuous_cos
    exact intervalStieltjesIntegral_positiveVertex_coordinate K hab hturn f hf i
      (fun u ↦ tangentVector u i) hQi E hE hEa
  rw [Fin.sum_univ_two, hcoord 0, hcoord 1]
  have h0 : Integrable (fun u : Real.Angle ↦ tangentVector u 0 * tangentVector u 0)
      (surfaceAreaMeasure K) := by
    apply Continuous.integrable_of_hasCompactSupport
    · convert Real.Angle.continuous_sin.mul Real.Angle.continuous_sin using 1
      funext u
      simp [tangentVector, frame]
    · exact isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
  have h1 : Integrable (fun u : Real.Angle ↦ tangentVector u 1 * tangentVector u 1)
      (surfaceAreaMeasure K) := by
    apply Continuous.integrable_of_hasCompactSupport
    · convert Real.Angle.continuous_cos.mul Real.Angle.continuous_cos using 1
      funext u
      simp [tangentVector, frame]
    · exact isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
  rw [← integral_add h0.integrableOn h1.integrableOn]
  have hone : (fun u : Real.Angle ↦
      tangentVector u 0 * tangentVector u 0 + tangentVector u 1 * tangentVector u 1) = 1 := by
    funext u
    simpa [tangentVector, frame, pow_two, add_comm] using u.cos_sq_add_sin_sq
  rw [hone]
  let S := (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E
  calc
    integral ((surfaceAreaMeasure K).restrict S) 1 =
        ((surfaceAreaMeasure K).restrict S).real univ := by
          change (∫ _ : Real.Angle, (1 : ℝ) ∂(surfaceAreaMeasure K).restrict S) = _
          rw [integral_const (μ := (surfaceAreaMeasure K).restrict S) (1 : ℝ),
            smul_eq_mul, mul_one]
    _ = (surfaceAreaMeasure K).real S :=
      measureReal_restrict_apply_univ (μ := surfaceAreaMeasure K) S
    _ = (surfaceAreaMeasure K S).toReal := measureReal_def _ _

/-- Pairing the positive-vertex Stieltjes measure with the normal frame vanishes. -/
theorem sum_intervalStieltjesIntegral_positiveVertex_normal
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ (i : Fin 2) (E : Set (Icc a b)), MeasurableSet E →
      (∀ t ∈ E, a < (t : ℝ)) →
      intervalStieltjesMeasure (f i) E =
        ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i ∂surfaceAreaMeasure K)
    (E : Set (Icc a b)) (hE : MeasurableSet E) (hEa : ∀ t ∈ E, a < (t : ℝ)) :
    (∑ i : Fin 2, intervalStieltjesIntegral (f i)
      (fun t ↦ normalVector (((t : ℝ) : Real.Angle)) i) E) = 0 := by
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hcoord (i : Fin 2) :
      intervalStieltjesIntegral (f i)
          (fun t ↦ normalVector (((t : ℝ) : Real.Angle)) i) E =
        ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          normalVector u i * tangentVector u i ∂surfaceAreaMeasure K := by
    have hQi : Continuous (fun u : Real.Angle ↦ normalVector u i) := by
      fin_cases i
      · exact Real.Angle.continuous_cos
      · exact Real.Angle.continuous_sin
    exact intervalStieltjesIntegral_positiveVertex_coordinate K hab hturn f hf i
      (fun u ↦ normalVector u i) hQi E hE hEa
  rw [Fin.sum_univ_two, hcoord 0, hcoord 1]
  have h0 : Integrable (fun u : Real.Angle ↦ normalVector u 0 * tangentVector u 0)
      (surfaceAreaMeasure K) := by
    apply Continuous.integrable_of_hasCompactSupport
    · convert (Real.Angle.continuous_cos.mul Real.Angle.continuous_sin).neg using 1
      funext u
      simp [normalVector, tangentVector, frame]
    · exact isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
  have h1 : Integrable (fun u : Real.Angle ↦ normalVector u 1 * tangentVector u 1)
      (surfaceAreaMeasure K) := by
    apply Continuous.integrable_of_hasCompactSupport
    · convert Real.Angle.continuous_sin.mul Real.Angle.continuous_cos using 1
      funext u
      simp [normalVector, tangentVector, frame]
    · exact isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
  rw [← integral_add h0.integrableOn h1.integrableOn]
  apply integral_eq_zero_of_ae
  filter_upwards with u
  simp [normalVector, tangentVector, frame]
  ring

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Cap.Contacts`.
* `Cap.ArmCoordinates`.
* `Cap.ContactIdentities`.
* `Cap.HalfPlanes`.
* `Cap.FanProjection`.
* `Cap.HallwayQuadrant`.
* `Cap.LowerNormalMeasure`.
* `Cap.ReflectionGeometry`.
* `Cap.SupportIntersections`.
* `Cap.TopCorner`.
* `Cap.Vertical`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Contacts
-/

public section

noncomputable section

namespace MovingSofa

/-- Width in a normal direction, for geometric use on nonempty compact sets. -/
@[expose]
def directionalWidth (s : Set Point) (t : Real.Angle) : ℝ :=
  supportValue s t + supportValue s (t + ((Real.pi : ℝ) : Real.Angle))

/-- The positive/negative contacts at the two outer supporting walls. -/
@[expose]
def capVertices {ω : ℝ} (K : CapSpace ω) (t : ℝ) : (Point × Point) × (Point × Point) :=
  (edgeVertices K.1 (t : Real.Angle),
    edgeVertices K.1 ((t + Real.pi / 2 : ℝ) : Real.Angle))

/-- The positive/negative right and left tangent arm lengths of a right-angle cap. -/
@[expose]
def tangentArmLengths (K : RightAngleCapSpace) (t : ℝ) : (ℝ × ℝ) × (ℝ × ℝ) :=
  let y := (rotatingHallwayParts (K.1 : Set Point) (t : Real.Angle)).outerCorner
  let v := capVertices K t
  ((inner ℝ (y - v.1.1) (tangentVector (t : Real.Angle)),
    inner ℝ (y - v.1.2) (tangentVector (t : Real.Angle))),
    (inner ℝ (y - v.2.1) (normalVector (t : Real.Angle)),
      inner ℝ (y - v.2.2) (normalVector (t : Real.Angle))))

/-- The open inner quadrant clipped by the fan. -/
@[expose]
def capWedge {ω : ℝ} (K : CapSpace ω) (t : ℝ) : Set Point :=
  capFan ω ∩ (rotatingHallwayParts (K.1 : Set Point) (t : Real.Angle)).innerQuadrant

/-- The two inner-wall intersections with the lower fan boundary lines. -/
@[expose]
def wedgeEndpoints {ω : ℝ} (K : CapSpace ω) (t : ℝ) : Point × Point :=
  (((supportValue K.1 (t : Real.Angle) - 1) / Real.cos t) • normalVector 0,
    ((supportValue K.1 ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
      Real.cos (ω - t)) • tangentVector (ω : Real.Angle))

/-- Signed right and left gaps between the wedge endpoints and bottom cap contacts. -/
@[expose]
def wedgeGaps {ω : ℝ} (K : CapSpace ω) (t : ℝ) : ℝ × ℝ :=
  (inner ℝ ((capVertices K 0).1.2 - (wedgeEndpoints K t).1) (normalVector 0),
    inner ℝ ((capVertices K ω).2.1 - (wedgeEndpoints K t).2)
      (tangentVector (ω : Real.Angle)))

/-- The selected short boundary arc, including only the specified endpoints. -/
@[expose]
def convexBoundaryArc (K : ConvexBody Point) (a b : ℝ) : Set Point :=
  {(edgeVertices K (a : Real.Angle)).1} ∪
    (⋃ t ∈ Set.Ioo a b, exposedEdge K (t : Real.Angle)) ∪
    {(edgeVertices K (b : Real.Angle)).2}

/-- The right wedge gap in support-function coordinates. -/
theorem wedgeGaps_fst_eq_supportValue {ω : ℝ} (K : CapSpace ω) (t : ℝ) :
    (wedgeGaps K t).1 = supportValue K.val (0 : Real.Angle) -
      (supportValue K.val (t : Real.Angle) - 1) / Real.cos t := by
  have hA := (edgeVertices_snd_mem K.val (0 : Real.Angle)).2
  change inner ℝ (capVertices K 0).1.2 (normalVector (0 : Real.Angle)) =
    supportValue K.val (0 : Real.Angle) at hA
  simp only [wedgeGaps, wedgeEndpoints, inner_sub_left, real_inner_smul_left, hA]
  have hu0 : inner ℝ (normalVector (0 : Real.Angle))
      (normalVector (0 : Real.Angle)) = 1 := by
    rw [← Real.Angle.coe_zero]
    exact inner_normalVector_self 0
  rw [hu0]
  ring

/-- The left wedge gap in support-function coordinates. -/
theorem wedgeGaps_snd_eq_supportValue {ω : ℝ} (K : CapSpace ω)
    (t : ℝ) :
    (wedgeGaps K t).2 =
      supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
        (supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
          Real.cos (ω - t) := by
  have hC := (edgeVertices_fst_mem K.val
    ((ω + Real.pi / 2 : ℝ) : Real.Angle)).2
  change inner ℝ (capVertices K ω).2.1
      (normalVector ((ω + Real.pi / 2 : ℝ) : Real.Angle)) =
    supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) at hC
  simp only [normalVector, frame, Real.Angle.coe_add, Real.Angle.cos_add_pi_div_two,
    Real.Angle.sin_coe, Real.Angle.sin_add_pi_div_two, Real.Angle.cos_coe] at hC
  change inner ℝ (capVertices K ω).2.1 (tangentVector (ω : Real.Angle)) =
    supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) at hC
  simp only [wedgeGaps, wedgeEndpoints, inner_sub_left,
    real_inner_smul_left, hC]
  rw [inner_tangentVector_self]
  ring

/-- The right wedge endpoint lies on the horizontal axis, at the horizontal intercept of the right
inner wall. -/
theorem wedgeEndpoints_fst_coords {ω : ℝ} (K : CapSpace ω) (t : ℝ) :
    (wedgeEndpoints K t).1 0 = (supportValue K.val (t : Real.Angle) - 1) / Real.cos t ∧
      (wedgeEndpoints K t).1 1 = 0 := by
  constructor <;> simp [wedgeEndpoints, normalVector, frame]

/-- For a right-angle cap the left wedge endpoint also lies on the horizontal axis, at the
horizontal intercept of the left inner wall. -/
theorem wedgeEndpoints_snd_coords (K : RightAngleCapSpace) (t : ℝ) :
    (wedgeEndpoints K t).2 0 =
        -((supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) / Real.sin t) ∧
      (wedgeEndpoints K t).2 1 = 0 := by
  constructor <;> simp [wedgeEndpoints, tangentVector, frame, Real.cos_pi_div_two_sub]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Arm Coordinates
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- Express the two positive arm lengths through support and moving-frame coordinates. -/
theorem tangentArmLengths_positive_frame (K : RightAngleCapSpace) (t : ℝ) :
    (tangentArmLengths K t).1.1 =
        supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) -
          inner ℝ (edgeVertices K.val (t : Real.Angle)).1
            (tangentVector (t : Real.Angle)) ∧
    (tangentArmLengths K t).2.1 =
        inner ℝ (edgeVertices K.val (t : Real.Angle)).1
            (normalVector (t : Real.Angle)) +
          inner ℝ (edgeVertices K.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).1
            (tangentVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) := by
  have hnn := inner_normalVector_self t
  have htt := inner_tangentVector_self t
  have hnt := inner_normalVector_tangentVector t
  have htn : inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (t : Real.Angle)) = 0 := by
    rw [real_inner_comm, hnt]
  have hA := (edgeVertices_fst_mem K.val (t : Real.Angle)).2
  simp only [tangentArmLengths, capVertices, outerCorner_eq_support_sum,
    inner_sub_left, inner_add_left, real_inner_smul_left, hnn, htt, hnt, htn]
  rw [hA, tangentVector_add_pi_div_two]
  simp [real_inner_comm]
  ring

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Contact Identities
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

theorem capTangentArm_identities (K : RightAngleCapSpace) (t : ℝ) :
    (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner =
      (capVertices K t).1.1 + (tangentArmLengths K t).1.1 • tangentVector (t : Real.Angle) ∧
    (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner =
      (capVertices K t).1.2 + (tangentArmLengths K t).1.2 • tangentVector (t : Real.Angle) ∧
    (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner =
      (capVertices K t).2.1 + (tangentArmLengths K t).2.1 • normalVector (t : Real.Angle) ∧
    (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner =
      (capVertices K t).2.2 + (tangentArmLengths K t).2.2 • normalVector (t : Real.Angle) := by
  have hrot : rotationMap (t : Real.Angle) (!₂[1, 1] : Point) =
      normalVector (t : Real.Angle) + tangentVector (t : Real.Angle) := by
    unfold rotationMap
    rw [Orientation.rotation_apply, rightAngleRotation_apply]
    ext i
    fin_cases i <;> simp [normalVector, tangentVector, frame]
    ring
  have hy : (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner =
      supportValue K.val (t : Real.Angle) • normalVector (t : Real.Angle) +
      supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) • tangentVector (t : Real.Angle) := by
    simp only [rotatingHallwayParts, supportingPlacement, hallwayParts, hrot, Real.Angle.coe_add]
    module
  have hnn : inner ℝ (normalVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = 1 := by
    rw [PiLp.inner_apply]
    simp [normalVector, frame, Fin.sum_univ_two, Real.cos_sq_add_sin_sq]
  have htt : inner ℝ (tangentVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = 1 := by
    rw [PiLp.inner_apply]
    simp [tangentVector, frame, Fin.sum_univ_two, Real.sin_sq_add_cos_sq]
  have hnt : inner ℝ (normalVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = 0 := by
    simp [normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
    ring
  have htn : inner ℝ (tangentVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = 0 := by
    rw [real_inner_comm, hnt]
  have hA (a b c : ℝ) :
      a • normalVector (t : Real.Angle) + b • tangentVector (t : Real.Angle) =
      (a • normalVector (t : Real.Angle) + c • tangentVector (t : Real.Angle)) +
        inner ℝ ((a • normalVector (t : Real.Angle) + b • tangentVector (t : Real.Angle)) -
          (a • normalVector (t : Real.Angle) + c • tangentVector (t : Real.Angle)))
          (tangentVector (t : Real.Angle)) • tangentVector (t : Real.Angle) := by
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left, hnt, htt]
    module
  have hC (a b c : ℝ) :
      a • normalVector (t : Real.Angle) + b • tangentVector (t : Real.Angle) =
      (b • tangentVector (t : Real.Angle) + c • -normalVector (t : Real.Angle)) +
        inner ℝ ((a • normalVector (t : Real.Angle) + b • tangentVector (t : Real.Angle)) -
          (b • tangentVector (t : Real.Angle) + c • -normalVector (t : Real.Angle)))
          (normalVector (t : Real.Angle)) • normalVector (t : Real.Angle) := by
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left, inner_neg_left, hnn, htn]
    module
  have hv : tangentVector ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle)) =
      -normalVector (t : Real.Angle) := by
    ext i
    fin_cases i <;> simp [normalVector, tangentVector, frame,
      Real.Angle.sin_add_pi_div_two, Real.Angle.cos_add_pi_div_two]
  simp only [tangentArmLengths, hy, capVertices, edgeVertices]
  refine ⟨hA _ _ _, hA _ _ _, ?_, ?_⟩ <;>
    simp only [Real.Angle.coe_add, normalVector_add_pi_div_two, hv] <;>
    exact hC _ _ _

theorem surfaceAreaMeasure_atom_length (K : ConvexBody Point) (t : Real.Angle) :
    surfaceAreaMeasure K {t} = Measure.hausdorffMeasure 1 (exposedEdge K t) ∧
    surfaceAreaMeasure K {t} = ENNReal.ofReal (dist (edgeVertices K t).1 (edgeVertices K t).2) ∧
    (edgeVertices K t).1 = (edgeVertices K t).2 +
      (surfaceAreaMeasure K {t}).toReal • tangentVector t := by
  induction t using Real.Angle.induction_on with
  | _ t =>
    have hface : surfaceAreaMeasure K {(t : Real.Angle)} =
        Measure.hausdorffMeasure 1 (exposedEdge K (t : Real.Angle)) := by
      have h := (surfaceAreaMeasure_face_union K).2.2.2.2
        {(t : Real.Angle)} (measurableSet_singleton _) (Or.inr
          ⟨t, t, le_rfl, by linarith [Real.pi_pos], by simp⟩)
      simpa using h
    have hlength : surfaceAreaMeasure K {(t : Real.Angle)} =
        ENNReal.ofReal (dist (edgeVertices K (t : Real.Angle)).1
          (edgeVertices K (t : Real.Angle)).2) := by
      rw [hface, exposedEdge_eq_segment_edgeVertices, hausdorffMeasure_segment,
        edist_dist, dist_comm]
    refine ⟨hface, hlength, ?_⟩
    let S := (fun p ↦ inner ℝ p (tangentVector (t : Real.Angle))) ''
      exposedEdge K (t : Real.Angle)
    have hcompact : IsCompact S := (isCompact_exposedEdge K _).image
      (continuous_id.inner continuous_const)
    have hnonneg : 0 ≤ sSup S - sInf S := sub_nonneg.mpr
      (csInf_le_csSup ((exposedEdge_nonempty K _).image _) hcompact.bddBelow hcompact.bddAbove)
    have hdiff : (edgeVertices K (t : Real.Angle)).1 -
        (edgeVertices K (t : Real.Angle)).2 =
        (sSup S - sInf S) • tangentVector (t : Real.Angle) := by
      simp only [edgeVertices, S]
      module
    have hnorm : ‖tangentVector (t : Real.Angle)‖ = 1 := by
      have h := inner_tangentVector_self t
      rw [real_inner_self_eq_norm_sq] at h
      nlinarith [norm_nonneg (tangentVector (t : Real.Angle))]
    have hdist : dist (edgeVertices K (t : Real.Angle)).1
        (edgeVertices K (t : Real.Angle)).2 = sSup S - sInf S := by
      rw [dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg,
        hnorm, mul_one]
    rw [hlength, ENNReal.toReal_ofReal dist_nonneg, hdist]
    exact (sub_eq_iff_eq_add.mp hdiff).trans (add_comm _ _)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Half Planes
-/

public section

noncomputable section

namespace MovingSofa

/-- A finite set of allowed normals gives a finite supporting-half-plane representation. -/
theorem HasHalfPlaneRepresentation.finite_constraints
    {K : ConvexBody Point} {N : Set Real.Angle} (hN : N.Finite)
    (hK : HasHalfPlaneRepresentation K N) :
    ∃ constraints : Set (Real.Angle × ℝ), constraints.Finite ∧
      (∀ c ∈ constraints, c.1 ∈ N) ∧
      (K : Set Point) = ⋂ c ∈ constraints, normalHalfPlane c.1 c.2 false false := by
  obtain ⟨C, hC, hKC⟩ := hK
  refine ⟨(fun t ↦ (t, supportValue K t)) '' N, hN.image _, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact ht
  · ext x
    simp only [Set.mem_iInter]
    constructor
    · intro hx c hc
      obtain ⟨t, ht, rfl⟩ := hc
      change inner ℝ x (normalVector t) ≤ supportValue K t
      exact le_csSup ((K.isCompact.image
        (continuous_inner.comp (continuous_id.prodMk continuous_const))).bddAbove)
        ⟨x, hx, rfl⟩
    · intro hx
      rw [hKC]
      simp only [Set.mem_iInter]
      intro c hc
      have hxs := hx (c.1, supportValue K c.1) ⟨c.1, hC c hc, rfl⟩
      change inner ℝ x (normalVector c.1) ≤ supportValue K c.1 at hxs
      change inner ℝ x (normalVector c.1) ≤ c.2
      apply hxs.trans
      apply csSup_le (K.nonempty.image _)
      rintro z ⟨p, hp, rfl⟩
      rw [hKC] at hp
      exact Set.mem_iInter.mp (Set.mem_iInter.mp hp c) hc

/-- Translation preserves a half-plane representation's allowed normals. -/
theorem HasHalfPlaneRepresentation.translate {K : ConvexBody Point}
    {N : Set Real.Angle} (hK : HasHalfPlaneRepresentation K N) (v : Point) :
    HasHalfPlaneRepresentation (ConvexBody.translate K v) N := by
  obtain ⟨C, hC, hKC⟩ := hK
  refine ⟨(fun c ↦ (c.1, c.2 + inner ℝ v (normalVector c.1))) '' C, ?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact hC c hc
  · ext x
    simp only [ConvexBody.translate, Set.mem_image, Set.mem_iInter]
    constructor
    · rintro ⟨y, hy, rfl⟩ c ⟨d, hd, rfl⟩
      change inner ℝ (y + v) (normalVector d.1) ≤
        d.2 + inner ℝ v (normalVector d.1)
      rw [inner_add_left]
      have hmem := Set.mem_iInter.mp (Set.mem_iInter.mp (hKC ▸ hy) d) hd
      change inner ℝ y (normalVector d.1) ≤ d.2 at hmem
      simpa [add_comm] using add_le_add_right hmem (inner ℝ v (normalVector d.1))
    · intro hx
      refine ⟨x - v, ?_, by simp⟩
      rw [hKC]
      simp only [Set.mem_iInter]
      intro c hc
      have h := hx (c.1, c.2 + inner ℝ v (normalVector c.1)) ⟨c, hc, rfl⟩
      change inner ℝ x (normalVector c.1) ≤
        c.2 + inner ℝ v (normalVector c.1) at h
      change inner ℝ (x - v) (normalVector c.1) ≤ c.2
      rw [inner_sub_left]
      linarith

/-- A normalized cap is contained in its lower fan. -/
theorem CapSpace.subset_capFan {ω : ℝ} (K : CapSpace ω) :
    (K.val : Set Point) ⊆ capFan ω := by
  intro p hp
  constructor
  · change 0 ≤ inner ℝ p (normalVector (ω : Real.Angle))
    have h := inner_le_supportValue K.val hp ((ω + Real.pi : ℝ) : Real.Angle)
    rw [K.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right] at h
    linarith
  · change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
    have h := inner_le_supportValue K.val hp ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    have hang : (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) =
        ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
      congr 1
      ring
    rw [K.property.2.2.2.2.2.1, ← hang] at h
    rw [normalVector_add_pi, inner_neg_right] at h
    linarith

/-- Fan membership and strict upper support inequalities imply cap membership. -/
theorem CapSpace.mem_of_mem_capFan_of_lt_supportValue {ω : ℝ}
    (K : CapSpace ω) {p : Point} (hp : p ∈ capFan ω)
    (hupper : ∀ t ∈ Set.Icc 0 (ω + Real.pi / 2),
      inner ℝ p (normalVector (t : Real.Angle)) < supportValue K.val (t : Real.Angle)) :
    p ∈ (K.val : Set Point) := by
  obtain ⟨C, hCN, hKC⟩ := K.property.2.2.2.2.2.2
  rw [hKC]
  simp only [Set.mem_iInter]
  intro c hc
  have hsupport : supportValue K.val c.1 ≤ c.2 := by
    apply supportValue_le_of_subset_normalHalfPlane
    intro q hq
    rw [hKC] at hq
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hq c) hc
  rcases hCN c hc with hcupper | hclower
  · obtain ⟨t, ht, heq⟩ := hcupper
    rw [← heq] at hsupport ⊢
    have htI : t ∈ Set.Icc 0 (ω + Real.pi / 2) := by
      rcases ht with ht | ht
      · exact ⟨ht.1, ht.2.trans (le_add_of_nonneg_right (by positivity))⟩
      · exact ⟨(by positivity : 0 ≤ Real.pi / 2).trans ht.1, ht.2⟩
    change inner ℝ p (normalVector (t : Real.Angle)) ≤ c.2
    exact (hupper t htI).le.trans hsupport
  · rcases hclower with hclower | hclower
    · rw [hclower] at hsupport ⊢
      change inner ℝ p (normalVector ((ω + Real.pi : ℝ) : Real.Angle)) ≤ c.2
      rw [normalVector_add_pi, inner_neg_right]
      have hpω := hp.1
      change 0 ≤ inner ℝ p (normalVector (ω : Real.Angle)) at hpω
      rw [K.property.2.2.2.2.1] at hsupport
      linarith [hsupport]
    · rw [hclower] at hsupport ⊢
      have hang : (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) =
          ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
        congr 1
        ring
      change inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤ c.2
      rw [← hang, normalVector_add_pi, inner_neg_right]
      have hpT := hp.2
      change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hpT
      rw [K.property.2.2.2.2.2.1] at hsupport
      linarith [hsupport]

/-- A normalized cap lies in the intersection of its two unit strips. -/
theorem CapSpace.subset_stripParallelogram {ω : ℝ} (K : CapSpace ω) :
    (K.val : Set Point) ⊆ (stripParallelogram ω).1 := by
  intro p hp
  have hlower := inner_le_supportValue K.val hp ((ω + Real.pi : ℝ) : Real.Angle)
  have hbottom := inner_le_supportValue K.val hp ((3 * Real.pi / 2 : ℝ) : Real.Angle)
  rw [K.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right] at hlower
  rw [K.property.2.2.2.2.2.1, inner_normalVector_three_pi_div_two] at hbottom
  have hupper := inner_le_supportValue K.val hp ((Real.pi / 2 : ℝ) : Real.Angle)
  have hright := inner_le_supportValue K.val hp (ω : Real.Angle)
  rw [K.property.2.2.2.1] at hupper
  rw [K.property.2.2.1] at hright
  rw [mem_stripParallelogram_iff]
  have hlo : 0 ≤ p 1 := by linarith
  have hhi : p 1 ≤ 1 := by
    simpa [normalVector, frame, PiLp.inner_apply] using hupper
  exact ⟨⟨hlo, hhi⟩, by linarith, hright⟩

/-- A half-plane representation can be tightened at every allowed normal. -/
theorem HasHalfPlaneRepresentation.eq_iInter_supportValue {K : ConvexBody Point}
    {N : Set Real.Angle} (hK : HasHalfPlaneRepresentation K N) :
    (K : Set Point) = ⋂ t ∈ N, normalHalfPlane t (supportValue K t) false false := by
  obtain ⟨C, hCN, hKC⟩ := hK
  ext p
  simp only [Set.mem_iInter]
  constructor
  · intro hp t _
    exact inner_le_supportValue K hp t
  · intro hp
    rw [hKC]
    simp only [Set.mem_iInter]
    intro c hc
    have ht := hp c.1 (hCN c hc)
    change inner ℝ p (normalVector c.1) ≤ c.2
    apply ht.trans
    apply csSup_le (K.nonempty.image _)
    rintro _ ⟨q, hq, rfl⟩
    rw [hKC] at hq
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hq c) hc

/-- A fan point satisfying all upper supporting inequalities belongs to the cap. -/
theorem CapSpace.mem_of_mem_capFan_of_le_supportValue {ω : ℝ}
    (K : CapSpace ω) {p : Point} (hp : p ∈ capFan ω)
    (hupper : ∀ t ∈ capUpperAngles ω,
      inner ℝ p (normalVector (t : Real.Angle)) ≤ supportValue K.val (t : Real.Angle)) :
    p ∈ (K.val : Set Point) := by
  rw [K.property.2.2.2.2.2.2.eq_iInter_supportValue]
  simp only [Set.mem_iInter]
  intro a ha
  rcases ha with ⟨t, ht, rfl⟩ | ha
  · exact hupper t ht
  rcases ha with rfl | rfl
  · change inner ℝ p (normalVector ((ω + Real.pi : ℝ) : Real.Angle)) ≤
      supportValue K.val ((ω + Real.pi : ℝ) : Real.Angle)
    rw [K.property.2.2.2.2.1]
    rw [normalVector_add_pi, inner_neg_right]
    exact neg_nonpos.mpr hp.1
  · have hang : ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
        (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) := by
      congr 1
      ring
    change inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤
      supportValue K.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.property.2.2.2.2.2.1]
    rw [hang, normalVector_add_pi, inner_neg_right]
    exact neg_nonpos.mpr hp.2

/-- Upper support bounds supplied by the two unit-height constraints of a cap. -/
theorem CapSpace.supportValue_upper_bounds {ω t : ℝ} (K : CapSpace ω)
    (ht : t ∈ Set.Ioo 0 ω) :
    supportValue K.val (t : Real.Angle) ≤
        Real.cos t * supportValue K.val (0 : Real.Angle) + Real.sin t ∧
      supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) ≤
        Real.sin (ω - t) + Real.cos (ω - t) *
          supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) := by
  have hcost : 0 ≤ Real.cos t := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, ht.1], ht.2.trans_le K.property.2.1⟩).le
  have hsint : 0 ≤ Real.sin t := (Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith [ht.2, K.property.2.1, Real.pi_pos])).le
  have hcosδ : 0 ≤ Real.cos (ω - t) := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [sub_pos.mpr ht.2, Real.pi_pos],
      by linarith [ht.1, K.property.2.1]⟩).le
  have hsinδ : 0 ≤ Real.sin (ω - t) := (Real.sin_pos_of_pos_of_lt_pi
    (sub_pos.mpr ht.2) (by linarith [ht.1, K.property.2.1, Real.pi_pos])).le
  constructor
  · apply csSup_le (K.val.nonempty.image _)
    rintro _ ⟨p, hp, rfl⟩
    have hx := inner_le_supportValue K.val hp (0 : Real.Angle)
    have hy := inner_le_supportValue K.val hp ((Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.property.2.2.2.1] at hy
    simp [normalVector, frame, PiLp.inner_apply] at hx hy ⊢
    nlinarith
  · apply csSup_le (K.val.nonempty.image _)
    rintro _ ⟨p, hp, rfl⟩
    have hu := inner_le_supportValue K.val hp (ω : Real.Angle)
    have hv := inner_le_supportValue K.val hp
      ((ω + Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.property.2.2.1] at hu
    have hvec : normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle) =
        Real.sin (ω - t) • normalVector (ω : Real.Angle) +
          Real.cos (ω - t) • tangentVector (ω : Real.Angle) := by
      have h := normalVector_add_real ω (Real.pi / 2 - (ω - t))
      rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub] at h
      simpa only [show ω + (Real.pi / 2 - (ω - t)) = t + Real.pi / 2 by ring] using h
    change inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≤ _
    rw [hvec, inner_add_right, inner_smul_right, inner_smul_right]
    have hv' : inner ℝ p (tangentVector (ω : Real.Angle)) ≤
        supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) := by
      simpa [normalVector, tangentVector, frame, Real.Angle.cos_add_pi_div_two,
        Real.Angle.sin_add_pi_div_two] using hv
    nlinarith

/-- Every point of a cap lies above the horizontal base line. -/
theorem CapSpace.inner_normalVector_pi_div_two_nonneg {ω : ℝ} (K : CapSpace ω) {q : Point}
    (hq : q ∈ (K.1 : Set Point)) :
    0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) := (K.subset_capFan hq).2

/-- Lowering a point of a right-angle cap onto the base line keeps it inside the cap: every
upper normal of such a cap has nonnegative vertical component, so no upper constraint is
tightened, and the two base constraints of the fan coincide here and hold with equality. -/
theorem CapSpace.base_projection_mem (K : CapSpace (Real.pi / 2)) {q : Point}
    (hq : q ∈ (K.val : Set Point)) :
    q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle) ∈ (K.val : Set Point) := by
  have hq1 : 0 ≤ q 1 := by
    simpa only [inner_normalVector_pi_div_two] using K.inner_normalVector_pi_div_two_nonneg hq
  have hinner (s : ℝ) : inner ℝ (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      (normalVector (s : Real.Angle)) =
      inner ℝ q (normalVector (s : Real.Angle)) - q 1 * Real.sin s := by
    rw [inner_sub_left, real_inner_smul_left, inner_normalVector_normalVector,
      Real.cos_pi_div_two_sub]
  have hbase : inner ℝ (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    rw [hinner, inner_normalVector_pi_div_two, Real.sin_pi_div_two, mul_one, sub_self]
  refine K.mem_of_mem_capFan_of_le_supportValue ⟨?_, ?_⟩ ?_
  · change 0 ≤ inner ℝ _ (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
    rw [hbase]
  · change 0 ≤ inner ℝ _ (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
    rw [hbase]
  · intro s hs
    have hs' : 0 ≤ s ∧ s ≤ Real.pi := by
      rcases hs with hs | hs
      · exact ⟨hs.1, by linarith [hs.2, Real.pi_pos]⟩
      · exact ⟨by linarith [hs.1, Real.pi_pos], by linarith [hs.2]⟩
    have hsin : 0 ≤ Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi hs'.1 hs'.2
    rw [hinner]
    linarith [mul_nonneg hq1 hsin, inner_le_supportValue K.val hq (s : Real.Angle)]

/-- The top supporting line of a right-angle cap is the horizontal line of height one, so every
point attaining the support value at the vertical normal has height one. -/
theorem CapSpace.apply_one_eq_one (K : CapSpace (Real.pi / 2)) {p : Point}
    (hp : inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue (K.val : Set Point) ((Real.pi / 2 : ℝ) : Real.Angle)) : p 1 = 1 := by
  rwa [inner_normalVector_pi_div_two, K.property.2.2.2.1] at hp

/-- A singleton extreme face of a right-angle cap at a horizontal normal lies on the base line.
Lowering its unique point onto the base line keeps it in the cap, and a horizontal normal does not
see that vertical displacement, so the lowered point lies in the same face; the face being a
singleton, the displacement vanishes. -/
theorem CapSpace.edgeVertices_fst_apply_one_eq_zero (K : CapSpace (Real.pi / 2)) {s : ℝ}
    (hs : Real.sin s = 0)
    (hface : (edgeVertices K.val (s : Real.Angle)).1 = (edgeVertices K.val (s : Real.Angle)).2) :
    (edgeVertices K.val (s : Real.Angle)).1 1 = 0 := by
  have hmem := edgeVertices_fst_mem K.val (s : Real.Angle)
  have hkey : inner ℝ ((edgeVertices K.val (s : Real.Angle)).1 -
      (edgeVertices K.val (s : Real.Angle)).1 1 •
        normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) (normalVector (s : Real.Angle)) =
      supportValue (K.val : Set Point) (s : Real.Angle) := by
    rw [inner_sub_left, real_inner_smul_left, inner_normalVector_normalVector,
      Real.cos_pi_div_two_sub, hs, mul_zero, sub_zero]
    exact hmem.2
  have hlow : (edgeVertices K.val (s : Real.Angle)).1 -
      (edgeVertices K.val (s : Real.Angle)).1 1 •
        normalVector ((Real.pi / 2 : ℝ) : Real.Angle) ∈
      exposedEdge K.val (s : Real.Angle) := ⟨K.base_projection_mem hmem.1, hkey⟩
  rw [exposedEdge_eq_segment_edgeVertices, ← hface, segment_same, Set.mem_singleton_iff,
    sub_eq_self] at hlow
  have h := congrArg (fun p : Point ↦ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)))
    hlow
  rwa [real_inner_smul_left, inner_normalVector_self, mul_one, inner_zero_left] at h

/-- A convex body with vanishing base support value that is stable under vertical projection to
the base line is cut out by upper half-planes together with the base half-plane. -/
theorem hasHalfPlaneRepresentation_of_base_projection (M : ConvexBody Point)
    (hbase : supportValue M ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0)
    (hproj : ∀ q ∈ (M : Set Point),
      q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle) ∈ (M : Set Point)) :
    HasHalfPlaneRepresentation M
      (((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles (Real.pi / 2)) ∪
        capLowerNormals (Real.pi / 2)) := by
  -- At a right angle the allowed upper normals are exactly the angles of `[0, π]`.
  have hangle : ∀ s ∈ Set.Icc (0 : ℝ) Real.pi,
      ((s : ℝ) : Real.Angle) ∈
        (((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles (Real.pi / 2)) ∪
          capLowerNormals (Real.pi / 2)) := by
    intro s hs
    refine Or.inl ⟨s, ?_, rfl⟩
    rcases le_or_gt s (Real.pi / 2) with h | h
    · exact Or.inl ⟨hs.1, h⟩
    · exact Or.inr ⟨h.le, by linarith [hs.2]⟩
  -- The vertical projection keeps the horizontal coordinate and kills the vertical one.
  have hflat : ∀ q : Point,
      (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) 0 = q 0 ∧
        (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) 1 = 0 := by
    intro q
    constructor <;> simp [normalVector, frame]
  -- The two attained horizontal extrema, lowered onto the base line.
  obtain ⟨qR, hqR, hqRval⟩ := exists_mem_inner_eq_supportValue M ((0 : ℝ) : Real.Angle)
  obtain ⟨qL, hqL, hqLval⟩ := exists_mem_inner_eq_supportValue M ((Real.pi : ℝ) : Real.Angle)
  rw [inner_normalVector_zero] at hqRval
  rw [inner_normalVector_real, Real.cos_pi, Real.sin_pi] at hqLval
  refine ⟨(fun a : Real.Angle ↦ (a, supportValue M a)) ''
    ((((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles (Real.pi / 2)) ∪
      capLowerNormals (Real.pi / 2))), ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ha
  · ext p
    simp only [Set.mem_iInter]
    refine ⟨fun hp c hc ↦ ?_, fun hp ↦ ?_⟩
    · obtain ⟨a, -, rfl⟩ := hc
      exact inner_le_supportValue M hp a
    · have hpupper : ∀ s ∈ Set.Icc (0 : ℝ) Real.pi,
          inner ℝ p (normalVector ((s : ℝ) : Real.Angle)) ≤
            supportValue M ((s : ℝ) : Real.Angle) :=
        fun s hs ↦ hp _ ⟨_, hangle s hs, rfl⟩
      have hpbase := hp _ ⟨((3 * Real.pi / 2 : ℝ) : Real.Angle),
        Or.inr (Set.mem_insert_iff.2 (Or.inr rfl)), rfl⟩
      change inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤
        supportValue M ((3 * Real.pi / 2 : ℝ) : Real.Angle) at hpbase
      rw [inner_normalVector_three_pi_div_two, hbase] at hpbase
      have hp1 : 0 ≤ p 1 := by linarith
      have hpR : p 0 ≤ qR 0 := by
        have h := hpupper 0 ⟨le_rfl, Real.pi_pos.le⟩
        rw [inner_normalVector_zero, ← hqRval] at h
        exact h
      have hpL : qL 0 ≤ p 0 := by
        have h := hpupper Real.pi ⟨Real.pi_pos.le, le_rfl⟩
        rw [inner_normalVector_real, Real.cos_pi, Real.sin_pi, ← hqLval] at h
        linarith
      rw [M.eq_iInter_halfSpaces]
      simp only [Set.mem_iInter]
      intro u hu
      obtain ⟨θ, rfl⟩ := exists_angle_normalVector_eq hu
      change inner ℝ p (normalVector θ) ≤ supportValue M θ
      rw [← Real.Angle.coe_toReal θ]
      set s : ℝ := θ.toReal
      rcases le_or_gt 0 s with hs0 | hs0
      · exact hpupper s ⟨hs0, Real.Angle.toReal_le_pi θ⟩
      · have hsin : Real.sin s < 0 :=
          Real.sin_neg_of_neg_of_neg_pi_lt hs0 (Real.Angle.neg_pi_lt_toReal θ)
        rw [inner_normalVector_real]
        rcases le_or_gt 0 (Real.cos s) with hc | hc
        · have h := inner_le_supportValue M (hproj qR hqR) ((s : ℝ) : Real.Angle)
          rw [inner_normalVector_real, (hflat qR).1, (hflat qR).2] at h
          nlinarith [mul_le_mul_of_nonneg_right hpR hc,
            mul_nonpos_of_nonneg_of_nonpos hp1 hsin.le]
        · have h := inner_le_supportValue M (hproj qL hqL) ((s : ℝ) : Real.Angle)
          rw [inner_normalVector_real, (hflat qL).1, (hflat qL).2] at h
          nlinarith [mul_le_mul_of_nonpos_right hpL hc.le,
            mul_nonpos_of_nonneg_of_nonpos hp1 hsin.le]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Fan Projection
-/

public section

noncomputable section

namespace MovingSofa

/-- Support values in the upper angular range of a non-right cap are nonnegative. -/
theorem supportValue_nonneg_of_mem_capUpperAngles {ω : ℝ} (K : CapSpace ω)
    (hω : ω < Real.pi / 2) {φ : ℝ} (hφ : φ ∈ capUpperAngles ω) :
    0 ≤ supportValue K.val (φ : Real.Angle) := by
  have hcosω : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [K.property.1, Real.pi_pos], hω⟩
  rcases hφ with hφ | hφ
  · obtain ⟨p, hpK, hpnormal⟩ := exists_mem_inner_eq_supportValue K.val
      ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    have hpFan := K.subset_capFan hpK
    have hpy : p 1 = 0 := by
      change inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue K.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) at hpnormal
      rw [K.property.2.2.2.2.2.1] at hpnormal
      have hang : ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
          (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) := by
        congr 1
        ring
      rw [hang, normalVector_add_pi, inner_neg_right] at hpnormal
      simpa [normalVector, frame, PiLp.inner_apply] using hpnormal
    have hpx : 0 ≤ p 0 := by
      have hpω := hpFan.1
      change 0 ≤ inner ℝ p (normalVector (ω : Real.Angle)) at hpω
      simp [normalVector, frame, PiLp.inner_apply, hpy] at hpω
      by_contra hneg
      have := mul_neg_of_pos_of_neg hcosω (lt_of_not_ge hneg)
      linarith
    have hcosφ : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc
      ⟨(neg_nonpos.mpr (by positivity : 0 ≤ Real.pi / 2)).trans hφ.1,
        hφ.2.trans hω.le⟩
    have hinner : 0 ≤ inner ℝ p (normalVector (φ : Real.Angle)) := by
      simp only [normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe, PiLp.inner_apply,
        RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, hpy, mul_zero, add_zero]
      exact mul_nonneg hcosφ hpx
    exact hinner.trans (inner_le_supportValue K.val hpK (φ : Real.Angle))
  · obtain ⟨p, hpK, hpnormal⟩ := exists_mem_inner_eq_supportValue K.val
      ((ω + Real.pi : ℝ) : Real.Angle)
    have hpFan := K.subset_capFan hpK
    have hpu : inner ℝ p (normalVector (ω : Real.Angle)) = 0 := by
      change inner ℝ p (normalVector ((ω + Real.pi : ℝ) : Real.Angle)) =
        supportValue K.val ((ω + Real.pi : ℝ) : Real.Angle) at hpnormal
      rw [K.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right] at hpnormal
      linarith
    let μ := inner ℝ p (tangentVector (ω : Real.Angle))
    have hp : μ • tangentVector (ω : Real.Angle) = p := by
      have hframe := inner_normalVector_smul_add_inner_tangentVector_smul
        p (ω : Real.Angle)
      rw [hpu, zero_smul, zero_add] at hframe
      exact hframe
    have hμ : 0 ≤ μ := by
      have hpy := hpFan.2
      change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hpy
      have hp1 := congrArg (fun q : Point ↦ q 1) hp
      change μ * Real.cos ω = p 1 at hp1
      have hpy' : 0 ≤ p 1 := by
        simpa [normalVector, frame, PiLp.inner_apply] using hpy
      rw [← hp1] at hpy'
      by_contra hneg
      have := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hcosω
      linarith
    have hsin : 0 ≤ Real.sin (φ - ω) := Real.sin_nonneg_of_nonneg_of_le_pi
      (by linarith [hφ.1]) (by linarith [hφ.2, Real.pi_pos])
    have hinner : 0 ≤ inner ℝ p (normalVector (φ : Real.Angle)) := by
      have htv : inner ℝ (tangentVector (ω : Real.Angle))
          (normalVector (φ : Real.Angle)) = Real.sin (φ - ω) := by
        simp [tangentVector, normalVector, frame, PiLp.inner_apply, Real.sin_sub]
        ring
      have heq : inner ℝ p (normalVector (φ : Real.Angle)) = μ * Real.sin (φ - ω) := by
        rw [← hp, real_inner_smul_left, htv]
      rw [heq]
      exact mul_nonneg hμ hsin
    exact hinner.trans (inner_le_supportValue K.val hpK (φ : Real.Angle))

/-- The origin belongs to every cap of angle strictly below a right angle. -/
theorem zero_mem_cap_of_lt {ω : ℝ} (K : CapSpace ω)
    (hω : ω < Real.pi / 2) : (0 : Point) ∈ (K.val : Set Point) := by
  apply K.mem_of_mem_capFan_of_le_supportValue
  · simp [capFan, normalHalfPlane]
  · intro φ hφ
    simpa using supportValue_nonneg_of_mem_capUpperAngles K hω hφ

/-- The normal projection of the zero-angle support value belongs to the cap. -/
theorem supportValue_zero_smul_normalVector_mem {ω : ℝ} (K : CapSpace ω) :
    supportValue K.val (0 : Real.Angle) • normalVector (0 : Real.Angle) ∈
      (K.val : Set Point) := by
  obtain ⟨p, hpK, hpnormal⟩ :=
    exists_mem_inner_eq_supportValue K.val (0 : Real.Angle)
  have hpFan := K.subset_capFan hpK
  have hpx : p 0 = supportValue K.val (0 : Real.Angle) := by
    change inner ℝ p (normalVector (0 : Real.Angle)) = supportValue K.val (0 : Real.Angle)
      at hpnormal
    simpa [normalVector, frame, PiLp.inner_apply] using hpnormal
  have hpy : 0 ≤ p 1 := by
    have := hpFan.2
    change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at this
    simpa [normalVector, frame, PiLp.inner_apply] using this
  apply K.mem_of_mem_capFan_of_le_supportValue
  · constructor
    · change 0 ≤ inner ℝ (supportValue K.val (0 : Real.Angle) •
          normalVector (0 : Real.Angle)) (normalVector (ω : Real.Angle))
      by_cases hω : ω = Real.pi / 2
      · simp [normalVector, frame, PiLp.inner_apply, hω]
      · have hωlt : ω < Real.pi / 2 := K.property.2.1.lt_of_ne hω
        have hs : 0 ≤ supportValue K.val (0 : Real.Angle) :=
          supportValue_nonneg_of_mem_capUpperAngles K hωlt
            (Or.inl ⟨le_rfl, K.property.1.le⟩)
        simp only [real_inner_smul_left]
        simp only [normalVector, frame, Real.Angle.cos_zero, Real.Angle.sin_zero, neg_zero,
          Real.Angle.cos_coe, Real.Angle.sin_coe, PiLp.inner_apply, RCLike.inner_apply,
          conj_trivial, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, mul_one,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, add_zero, ge_iff_le]
        exact mul_nonneg hs (Real.cos_nonneg_of_mem_Icc
          ⟨by linarith [K.property.1, Real.pi_pos], K.property.2.1⟩)
    · change 0 ≤ inner ℝ (supportValue K.val (0 : Real.Angle) •
          normalVector (0 : Real.Angle))
        (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      simp [normalVector, frame, PiLp.inner_apply]
  · intro φ hφ
    have hφI : φ ∈ Set.Icc 0 Real.pi := by
      rcases hφ with hφ | hφ
      · exact ⟨hφ.1, hφ.2.trans
          (K.property.2.1.trans (by linarith [Real.pi_pos]))⟩
      · exact ⟨(by positivity : 0 ≤ Real.pi / 2).trans hφ.1,
          hφ.2.trans (by linarith [K.property.2.1, Real.pi_pos])⟩
    have hsinφ : 0 ≤ Real.sin φ := Real.sin_nonneg_of_mem_Icc hφI
    have hbound := inner_le_supportValue K.val hpK (φ : Real.Angle)
    have hinner : inner ℝ
        (supportValue K.val (0 : Real.Angle) • normalVector (0 : Real.Angle))
        (normalVector (φ : Real.Angle)) ≤ inner ℝ p (normalVector (φ : Real.Angle)) := by
      simp only [normalVector, frame, Real.Angle.cos_zero, Real.Angle.sin_zero, neg_zero,
        Real.Angle.cos_coe, Real.Angle.sin_coe, PiLp.inner_apply, PiLp.smul_apply, smul_eq_mul,
        RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
        mul_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, add_zero, hpx,
        le_add_iff_nonneg_right]
      exact mul_nonneg hsinφ hpy
    exact hinner.trans hbound

/-- At a right angle, the opposite normal projection belongs to the cap. -/
theorem supportValue_pi_smul_normalVector_mem_of_eq {ω : ℝ} (K : CapSpace ω)
    (hω : ω = Real.pi / 2) :
    supportValue K.val (Real.pi : Real.Angle) • normalVector (Real.pi : Real.Angle) ∈
      (K.val : Set Point) := by
  obtain ⟨p, hpK, hpnormal⟩ :=
    exists_mem_inner_eq_supportValue K.val (Real.pi : Real.Angle)
  have hpFan := K.subset_capFan hpK
  have hpx : -p 0 = supportValue K.val (Real.pi : Real.Angle) := by
    change inner ℝ p (normalVector (Real.pi : Real.Angle)) =
      supportValue K.val (Real.pi : Real.Angle) at hpnormal
    simpa [normalVector, frame, PiLp.inner_apply] using hpnormal
  have hpy : 0 ≤ p 1 := by
    have := hpFan.2
    change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at this
    simpa [normalVector, frame, PiLp.inner_apply] using this
  apply K.mem_of_mem_capFan_of_le_supportValue
  · constructor <;>
      simp [normalHalfPlane, normalVector, frame, PiLp.inner_apply, hω]
  · intro φ hφ
    have hφI : φ ∈ Set.Icc 0 Real.pi := by
      rcases hφ with hφ | hφ
      · exact ⟨hφ.1, hφ.2.trans (by rw [hω]; linarith [Real.pi_pos])⟩
      · exact ⟨(by positivity : 0 ≤ Real.pi / 2).trans hφ.1,
          hφ.2.trans (by rw [hω]; linarith)⟩
    have hsinφ : 0 ≤ Real.sin φ := Real.sin_nonneg_of_mem_Icc hφI
    have hbound := inner_le_supportValue K.val hpK (φ : Real.Angle)
    have hinner : inner ℝ
        (supportValue K.val (Real.pi : Real.Angle) • normalVector (Real.pi : Real.Angle))
        (normalVector (φ : Real.Angle)) ≤ inner ℝ p (normalVector (φ : Real.Angle)) := by
      rw [← hpx]
      simp only [Fin.isValue, normalVector, frame, Real.Angle.cos_coe, Real.cos_pi,
        Real.Angle.sin_coe, Real.sin_pi, neg_zero, neg_smul, inner_neg_left, PiLp.inner_apply,
        PiLp.smul_apply, smul_eq_mul, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two,
        Matrix.cons_val_zero, mul_neg, mul_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        mul_zero, add_zero, neg_neg, le_add_iff_nonneg_right]
      exact mul_nonneg hsinφ hpy
    exact hinner.trans hbound

/-- For a non-right cap, the terminal tangent projection belongs to the cap. -/
theorem supportValue_add_pi_div_two_smul_tangentVector_mem_of_lt {ω : ℝ}
    (K : CapSpace ω) (hω : ω < Real.pi / 2) :
    supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) •
        tangentVector (ω : Real.Angle) ∈ (K.val : Set Point) := by
  have hcosω : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [K.property.1, Real.pi_pos], hω⟩
  let L := supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle)
  obtain ⟨p, hpK, hpnormal⟩ := exists_mem_inner_eq_supportValue K.val
    ((ω + Real.pi / 2 : ℝ) : Real.Angle)
  have hpFan := K.subset_capFan hpK
  have hpv : inner ℝ p (tangentVector (ω : Real.Angle)) = L := by
    change inner ℝ p (normalVector ((ω + Real.pi / 2 : ℝ) : Real.Angle)) = L at hpnormal
    rw [show ((ω + Real.pi / 2 : ℝ) : Real.Angle) =
      (ω : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) by rfl,
      normalVector_add_pi_div_two] at hpnormal
    exact hpnormal
  let a := inner ℝ p (normalVector (ω : Real.Angle))
  have ha : 0 ≤ a := hpFan.1
  have hp : a • normalVector (ω : Real.Angle) + L • tangentVector (ω : Real.Angle) = p := by
    simpa only [a, hpv] using
      inner_normalVector_smul_add_inner_tangentVector_smul p (ω : Real.Angle)
  have hL : 0 ≤ L := supportValue_nonneg_of_mem_capUpperAngles K hω
    (Or.inr ⟨by linarith [K.property.1, Real.pi_pos], le_rfl⟩)
  apply K.mem_of_mem_capFan_of_le_supportValue
  · constructor
    · change 0 ≤ inner ℝ (L • tangentVector (ω : Real.Angle))
        (normalVector (ω : Real.Angle))
      rw [real_inner_smul_left, real_inner_comm, inner_normalVector_tangentVector]
      simp
    · change 0 ≤ inner ℝ (L • tangentVector (ω : Real.Angle))
        (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      simp only [tangentVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe, normalVector,
        Real.cos_pi_div_two, Real.sin_pi_div_two, PiLp.inner_apply, PiLp.smul_apply,
        smul_eq_mul, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Fin.isValue,
        Matrix.cons_val_zero, mul_neg, zero_mul, neg_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, one_mul, zero_add]
      exact mul_nonneg hL hcosω.le
  · intro φ hφ
    have hdiff : φ - ω ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      rcases hφ with hφ | hφ
      · exact ⟨by linarith [hφ.1, K.property.2.1],
          by linarith [hφ.2, Real.pi_pos]⟩
      · exact ⟨by linarith [hφ.1, K.property.2.1, Real.pi_pos],
          by linarith [hφ.2]⟩
    have hcos : 0 ≤ Real.cos (φ - ω) := Real.cos_nonneg_of_mem_Icc hdiff
    have hnu : inner ℝ (normalVector (ω : Real.Angle))
        (normalVector (φ : Real.Angle)) = Real.cos (φ - ω) := by
      rw [inner_normalVector_normalVector]
      rw [show ω - φ = -(φ - ω) by ring, Real.cos_neg]
    have hbound := inner_le_supportValue K.val hpK (φ : Real.Angle)
    have hinner : inner ℝ (L • tangentVector (ω : Real.Angle))
        (normalVector (φ : Real.Angle)) ≤ inner ℝ p (normalVector (φ : Real.Angle)) := by
      rw [← hp, inner_add_left, real_inner_smul_left, real_inner_smul_left, hnu]
      exact le_add_of_nonneg_left (mul_nonneg ha hcos)
    exact hinner.trans hbound

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Hallway Quadrant
-/

public section

noncomputable section

namespace MovingSofa

/-- The inward quadrant of the supporting hallway at angle `t` is the inward quadrant of `s`
written in support-value coordinates. -/
theorem rotatingHallwayParts_innerQuadrant (s : Set Point) (t : ℝ) :
    (rotatingHallwayParts s (t : Real.Angle)).innerQuadrant = innerQuadrant s t := by
  rw [(rotatingHallwayParts_formulas s (t : Real.Angle)).2.2.2.2.2.2.2.2]
  simp only [innerQuadrant, Real.Angle.coe_add]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The surface area measure of a right-angle cap at its lower normals

A right-angle cap lies above its base line and is stable under vertical projection onto it, so
at a strictly downward normal direction the support value is attained only on the base line, at
whichever horizontal extremum the sign of the horizontal normal component selects.  Both open
quarter arcs of lower normals therefore carry faces that degenerate to a single base corner,
and the surface area measure vanishes on them
(`MovingSofa.CapSpace.surfaceAreaMeasure_image_Ioo_lower_eq_zero`).  Outside the closed upper
semicircle only the bottom normal `3π / 2` is left, so an integrand vanishing there integrates
to zero (`MovingSofa.CapSpace.setIntegral_compl_image_Icc_zero_pi_eq_zero`).
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- At a strictly downward normal direction the face of a right-angle cap degenerates to the
base point below a horizontal extremum: positive height strictly lowers the normal coordinate,
and on the base line the sign of `Real.cos t` selects a horizontal extremum. -/
theorem CapSpace.exposedEdge_subset_singleton_of_isMaxOn (K : CapSpace (Real.pi / 2))
    {q : Point} (hq : q ∈ (K.val : Set Point)) {t : ℝ} (hcos : Real.cos t ≠ 0)
    (hsin : Real.sin t < 0)
    (hmax : IsMaxOn (fun p : Point ↦ p 0 * Real.cos t) (K.val : Set Point) q) :
    exposedEdge K.val (t : Real.Angle) ⊆
      {q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)} := by
  have hflat0 : (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) 0 = q 0 := by
    simp [normalVector, frame]
  have hflat1 : (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) 1 = 0 := by
    simp [normalVector, frame]
  intro p hp
  have hpK : p ∈ (K.val : Set Point) := hp.1
  have hp1 : 0 ≤ p 1 := by
    simpa only [inner_normalVector_pi_div_two] using K.inner_normalVector_pi_div_two_nonneg hpK
  have hpsup : inner ℝ p (normalVector (t : Real.Angle)) =
    supportValue K.val (t : Real.Angle) := hp.2
  have hple : inner ℝ (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      (normalVector (t : Real.Angle)) ≤ inner ℝ p (normalVector (t : Real.Angle)) := by
    rw [hpsup]
    exact inner_le_supportValue K.val (K.base_projection_mem hq) _
  rw [inner_normalVector_real, inner_normalVector_real, hflat0, hflat1] at hple
  have h1 : p 0 * Real.cos t ≤ q 0 * Real.cos t := isMaxOn_iff.mp hmax p hpK
  have h2 : p 1 * Real.sin t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp1 hsin.le
  have he1 : p 0 * Real.cos t = q 0 * Real.cos t := by linarith
  have he2 : p 1 = 0 := by
    have h3 : p 1 * Real.sin t = 0 := by linarith
    exact (mul_eq_zero.mp h3).resolve_right hsin.ne
  have g0 : p 0 = (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) 0 := by
    rw [hflat0]; exact mul_right_cancel₀ hcos he1
  have g1 : p 1 = (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) 1 := by
    rw [hflat1]; exact he2
  have hpt : p = q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle) := by
    ext i
    fin_cases i
    · exact g0
    · exact g1
  simpa only [Set.mem_singleton_iff] using hpt

/-- The two base corners of a right-angle cap: on the open lower left quarter of normals every
face degenerates to the base point below a leftmost point of the cap, and on the open lower
right quarter to the base point below a rightmost one. -/
theorem CapSpace.exists_exposedEdge_subset_singleton (K : CapSpace (Real.pi / 2)) :
    ∃ pl pr : Point,
      (∀ t : ℝ, Real.cos t < 0 → Real.sin t < 0 →
        exposedEdge K.val (t : Real.Angle) ⊆ {pl}) ∧
      ∀ t : ℝ, 0 < Real.cos t → Real.sin t < 0 →
        exposedEdge K.val (t : Real.Angle) ⊆ {pr} := by
  have hcont : Continuous fun q : Point ↦ q 0 := PiLp.continuous_apply 2 _ 0
  obtain ⟨ql, hql, hqlmin⟩ :=
    K.val.isCompact.exists_isMinOn K.val.nonempty hcont.continuousOn
  obtain ⟨qr, hqr, hqrmax⟩ :=
    K.val.isCompact.exists_isMaxOn K.val.nonempty hcont.continuousOn
  refine ⟨ql - ql 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle),
    qr - qr 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle), ?_, ?_⟩
  · exact fun t hcos hsin ↦ K.exposedEdge_subset_singleton_of_isMaxOn hql hcos.ne hsin
      (isMaxOn_iff.mpr fun p hp ↦
        mul_le_mul_of_nonpos_right (isMinOn_iff.mp hqlmin p hp) hcos.le)
  · exact fun t hcos hsin ↦ K.exposedEdge_subset_singleton_of_isMaxOn hqr hcos.ne' hsin
      (isMaxOn_iff.mpr fun p hp ↦
        mul_le_mul_of_nonneg_right (isMaxOn_iff.mp hqrmax p hp) hcos.le)

/-- The surface area measure of a right-angle cap vanishes on both open quarter arcs of lower
normals, because there every face degenerates to a single base corner. -/
theorem CapSpace.surfaceAreaMeasure_image_Ioo_lower_eq_zero (K : CapSpace (Real.pi / 2)) :
    surfaceAreaMeasure K.val
        ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo Real.pi (3 * Real.pi / 2)) = 0 ∧
      surfaceAreaMeasure K.val
        ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo (3 * Real.pi / 2) (2 * Real.pi)) = 0 := by
  have hpi := Real.pi_pos
  obtain ⟨pl, pr, hl, hr⟩ := K.exists_exposedEdge_subset_singleton
  have hsin : ∀ s : ℝ, Real.pi < s → s < 2 * Real.pi → Real.sin s < 0 := by
    intro s h1 h2
    have h := Real.sin_pos_of_pos_of_lt_pi (x := s - Real.pi) (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at h
    linarith
  have main : ∀ (a b : ℝ) (p : Point), a ≤ b → b < a + Real.pi →
      (∀ s ∈ Set.Ioo a b, exposedEdge K.val (s : Real.Angle) ⊆ {p}) →
      surfaceAreaMeasure K.val ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b) = 0 := by
    intro a b p hab hba hsub
    refine surfaceAreaMeasure_null_of_exposedEdge_subset_singleton K.val
      (Real.Angle.isOpen_image_Ioo a b).measurableSet hab hba
      (Set.image_mono Set.Ioo_subset_Icc_self) p ?_
    intro u hu
    obtain ⟨s, hs, rfl⟩ := hu
    exact hsub s hs
  refine ⟨main Real.pi (3 * Real.pi / 2) pl (by linarith) (by linarith) fun s hs ↦ ?_,
    main (3 * Real.pi / 2) (2 * Real.pi) pr (by linarith) (by linarith) fun s hs ↦ ?_⟩
  · exact hl s (Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith [hs.1]) (by linarith [hs.2]))
      (hsin s hs.1 (by linarith [hs.2]))
  · refine hr s ?_ (hsin s (by linarith [hs.1]) hs.2)
    have h := Real.cos_pos_of_mem_Ioo
      (x := s - 2 * Real.pi) ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rwa [Real.cos_sub_two_pi] at h

/-- Outside the closed upper semicircle the surface area measure of a right-angle cap is carried
by the single downward normal `3π / 2`, so any integrand vanishing there integrates to zero. -/
theorem CapSpace.setIntegral_compl_image_Icc_zero_pi_eq_zero (K : CapSpace (Real.pi / 2))
    (f : Real.Angle → ℝ) (hf : f ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0) :
    ∫ t in ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc 0 Real.pi)ᶜ,
      f t ∂surfaceAreaMeasure K.val = 0 := by
  obtain ⟨hA, hB⟩ := K.surfaceAreaMeasure_image_Ioo_lower_eq_zero
  have hS : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc 0 Real.pi) :=
    (isCompact_Icc.image Real.Angle.continuous_coe).isClosed.measurableSet
  have haenot : ∀ᵐ t ∂surfaceAreaMeasure K.val,
      t ∉ ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo Real.pi (3 * Real.pi / 2)) ∪
        ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo (3 * Real.pi / 2) (2 * Real.pi)) := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using measure_union_null hA hB
  have hcongr : ∫ t in ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc 0 Real.pi)ᶜ,
      f t ∂surfaceAreaMeasure K.val =
      ∫ _t in ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc 0 Real.pi)ᶜ,
        (0 : ℝ) ∂surfaceAreaMeasure K.val := by
    refine setIntegral_congr_ae hS.compl ?_
    filter_upwards [haenot] with t ht hts
    have hcoe : ((t.toReal + 2 * Real.pi : ℝ) : Real.Angle) = t := by
      rw [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero, Real.Angle.coe_toReal]
    have hneg : t.toReal < 0 := by
      by_contra hge
      exact hts ⟨t.toReal, ⟨not_lt.mp hge, Real.Angle.toReal_le_pi t⟩, t.coe_toReal⟩
    have hlow : Real.pi < t.toReal + 2 * Real.pi :=
      by linarith [Real.Angle.neg_pi_lt_toReal t]
    have hmid : t = ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
      rcases lt_trichotomy (t.toReal + 2 * Real.pi) (3 * Real.pi / 2) with h | h | h
      · exact absurd (Or.inl ⟨t.toReal + 2 * Real.pi, ⟨hlow, h⟩, hcoe⟩) ht
      · rw [← hcoe, h]
      · exact absurd (Or.inr ⟨t.toReal + 2 * Real.pi, ⟨h, by linarith⟩, hcoe⟩) ht
    rw [hmid, hf]
  rw [hcongr, integral_zero]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Reflection Geometry
-/

public section

noncomputable section

namespace MovingSofa

/-- Image of a convex body under the cap reflection. -/
@[expose]
def reflectedBody (ω : ℝ) (K : ConvexBody Point) : ConvexBody Point where
  carrier := capReflection ω '' (K : Set Point)
  convex' := K.convex.linear_image (capReflection ω).toLinearEquiv.toLinearMap
  isCompact' := K.isCompact.image (capReflection ω).continuous
  nonempty' := K.nonempty.image _

/-- Support values of a reflected body are indexed by reflected normal angles. -/
theorem supportValue_reflectedBody (ω : ℝ) (K : ConvexBody Point)
    (a : Real.Angle) :
    supportValue (reflectedBody ω K) a =
      supportValue K (reflectedAngle ω a) := by
  unfold supportValue
  congr 1
  ext x
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q, hq, (inner_capReflection_normalVector ω q a).symm⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨capReflection ω q, ⟨q, hq, rfl⟩,
      inner_capReflection_normalVector ω q a⟩

/-- A reflected normal remains among the allowed cap normals. -/
theorem reflectedAngle_mem_capNormals {ω : ℝ} (a : Real.Angle)
    (ha : a ∈ ((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles ω) ∪
      capLowerNormals ω) :
    reflectedAngle ω a ∈
      ((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles ω) ∪
        capLowerNormals ω := by
  rcases ha with ha | ha
  · obtain ⟨t, ht, rfl⟩ := ha
    left
    refine ⟨ω + Real.pi / 2 - t, ?_, (reflectedAngle_coe ω t).symm⟩
    rcases ht with ht | ht
    · right
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    · left
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · right
    simp only [capLowerNormals, Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    rcases ha with rfl | rfl
    · right
      rw [reflectedAngle_coe]
      have hperiod :
          (((-Real.pi / 2 : ℝ) : Real.Angle)) =
            (((3 * Real.pi / 2 : ℝ) : Real.Angle)) := by
        calc
          (((-Real.pi / 2 : ℝ) : Real.Angle)) =
              (((-Real.pi / 2 + 2 * Real.pi : ℝ) : Real.Angle)) := by
                rw [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero]
          _ = (((3 * Real.pi / 2 : ℝ) : Real.Angle)) := by congr 1; ring
      convert hperiod using 1
      all_goals ring_nf
    · left
      rw [reflectedAngle_coe]
      have hperiod :
          (((ω - Real.pi : ℝ) : Real.Angle)) =
            (((ω + Real.pi : ℝ) : Real.Angle)) := by
        calc
          (((ω - Real.pi : ℝ) : Real.Angle)) =
              (((ω - Real.pi + 2 * Real.pi : ℝ) : Real.Angle)) := by
                rw [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero]
          _ = (((ω + Real.pi : ℝ) : Real.Angle)) := by congr 1; ring
      convert hperiod using 1
      all_goals ring_nf

/-- Reflect a half-plane presentation when its allowed normals are transported. -/
theorem HasHalfPlaneRepresentation.reflectedBody {ω : ℝ}
    {K : ConvexBody Point} {N N' : Set Real.Angle}
    (hK : HasHalfPlaneRepresentation K N)
    (hN : ∀ a ∈ N, reflectedAngle ω a ∈ N') :
    HasHalfPlaneRepresentation (reflectedBody ω K) N' := by
  obtain ⟨C, hCN, hKC⟩ := hK
  let ρ : Real.Angle × ℝ → Real.Angle × ℝ :=
    fun c ↦ (reflectedAngle ω c.1, c.2)
  refine ⟨ρ '' C, ?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact hN c.1 (hCN c hc)
  · ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      simp only [Set.mem_iInter]
      intro c hc
      obtain ⟨d, hd, rfl⟩ := hc
      change inner ℝ (capReflection ω q)
        (normalVector (reflectedAngle ω d.1)) ≤ d.2
      rw [inner_capReflection_normalVector, reflectedAngle_involutive]
      rw [hKC] at hq
      exact Set.mem_iInter.mp (Set.mem_iInter.mp hq d) hd
    · intro hp
      refine ⟨capReflection ω p, ?_, capReflection_involutive ω p⟩
      rw [hKC]
      simp only [Set.mem_iInter]
      intro c hc
      have hpc := Set.mem_iInter.mp
        (Set.mem_iInter.mp hp (ρ c)) ⟨c, hc, rfl⟩
      change inner ℝ p (normalVector (reflectedAngle ω c.1)) ≤ c.2 at hpc
      change inner ℝ (capReflection ω p) (normalVector c.1) ≤ c.2
      rw [inner_capReflection_normalVector]
      exact hpc

/-- Reflection preserves the standard cap half-plane presentation. -/
theorem reflectedBody_halfPlaneRepresentation {ω : ℝ}
    (K : ConvexBody Point)
    (hK : HasHalfPlaneRepresentation K
      (((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles ω) ∪
        capLowerNormals ω)) :
    HasHalfPlaneRepresentation (reflectedBody ω K)
      (((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles ω) ∪
        capLowerNormals ω) :=
  hK.reflectedBody fun a ha ↦ reflectedAngle_mem_capNormals a ha

/-- Reflection exchanges the normalized upper normal at `ω` with the vertical normal. -/
theorem reflectedAngle_at_omega (ω : ℝ) :
    reflectedAngle ω (ω : Real.Angle) =
      ((Real.pi / 2 : ℝ) : Real.Angle) := by
  rw [reflectedAngle_coe]
  congr 1
  ring

/-- Reflection exchanges the vertical normal with the normalized upper normal at `ω`. -/
theorem reflectedAngle_at_pi_div_two (ω : ℝ) :
    reflectedAngle ω ((Real.pi / 2 : ℝ) : Real.Angle) =
      (ω : Real.Angle) := by
  rw [reflectedAngle_coe]
  congr 1
  ring

/-- Reflection exchanges the two lower cap normals. -/
theorem reflectedAngle_at_omega_add_pi (ω : ℝ) :
    reflectedAngle ω ((ω + Real.pi : ℝ) : Real.Angle) =
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
  rw [reflectedAngle_coe]
  have hperiod :
      (((-Real.pi / 2 : ℝ) : Real.Angle)) =
        (((3 * Real.pi / 2 : ℝ) : Real.Angle)) := by
    calc
      (((-Real.pi / 2 : ℝ) : Real.Angle)) =
          (((-Real.pi / 2 + 2 * Real.pi : ℝ) : Real.Angle)) := by
            rw [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero]
      _ = (((3 * Real.pi / 2 : ℝ) : Real.Angle)) := by congr 1; ring
  convert hperiod using 1
  all_goals ring_nf

/-- Reflection exchanges the two lower cap normals. -/
theorem reflectedAngle_at_three_pi_div_two (ω : ℝ) :
    reflectedAngle ω ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
      ((ω + Real.pi : ℝ) : Real.Angle) := by
  rw [reflectedAngle_coe]
  have hperiod :
      (((ω - Real.pi : ℝ) : Real.Angle)) =
        (((ω + Real.pi : ℝ) : Real.Angle)) := by
    calc
      (((ω - Real.pi : ℝ) : Real.Angle)) =
          (((ω - Real.pi + 2 * Real.pi : ℝ) : Real.Angle)) := by
            rw [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero]
      _ = (((ω + Real.pi : ℝ) : Real.Angle)) := by congr 1; ring
  convert hperiod using 1
  all_goals ring_nf

/-- Reflection preserves the normalized cap conditions. -/
theorem reflectedBody_isCap {ω : ℝ} (K : CapSpace ω) :
    IsCap ω (reflectedBody ω K.val) := by
  rcases K.property with ⟨hω0, hωle, hω, hpi, hlowω, hlowpi, hrepr⟩
  refine ⟨hω0, hωle, ?_, ?_, ?_, ?_,
    reflectedBody_halfPlaneRepresentation K.val hrepr⟩
  · rw [supportValue_reflectedBody, reflectedAngle_at_omega, hpi]
  · rw [supportValue_reflectedBody, reflectedAngle_at_pi_div_two, hω]
  · rw [supportValue_reflectedBody, reflectedAngle_at_omega_add_pi, hlowpi]
  · rw [supportValue_reflectedBody, reflectedAngle_at_three_pi_div_two, hlowω]

/-- The cap reflection preserves the lower fan. -/
theorem capReflection_image_capFan (ω : ℝ) :
    capReflection ω '' capFan ω = capFan ω := by
  unfold capFan
  rw [Set.image_inter (capReflection ω).injective,
    capReflection_image_normalHalfPlane,
    capReflection_image_normalHalfPlane,
    reflectedAngle_at_omega, reflectedAngle_at_pi_div_two,
    Set.inter_comm]

/-- Reflection sends the complementary normal to its paired normal. -/
theorem reflectedAngle_sub (ω t : ℝ) :
    reflectedAngle ω ((ω - t : ℝ) : Real.Angle) =
      ((t + Real.pi / 2 : ℝ) : Real.Angle) := by
  rw [reflectedAngle_coe]
  congr 1
  ring

/-- Reflection sends the complementary paired normal back to the original normal. -/
theorem reflectedAngle_sub_add_pi_div_two (ω t : ℝ) :
    reflectedAngle ω ((ω - t + Real.pi / 2 : ℝ) : Real.Angle) =
      (t : Real.Angle) := by
  rw [reflectedAngle_coe]
  congr 1
  ring

/-- Reflection sends a paired normal to the complementary normal. -/
theorem reflectedAngle_add_pi_div_two (ω t : ℝ) :
    reflectedAngle ω ((t + Real.pi / 2 : ℝ) : Real.Angle) =
      ((ω - t : ℝ) : Real.Angle) := by
  rw [reflectedAngle_coe]
  congr 1
  ring

/-- Reflection transports inward quadrants at complementary angles. -/
theorem innerQuadrant_reflection (ω t : ℝ) (K : ConvexBody Point) :
    innerQuadrant (reflectedBody ω K) t =
      capReflection ω '' innerQuadrant K (ω - t) := by
  unfold innerQuadrant
  rw [Set.image_inter (capReflection ω).injective,
    capReflection_image_normalHalfPlane,
    capReflection_image_normalHalfPlane,
    supportValue_reflectedBody, supportValue_reflectedBody,
    reflectedAngle_sub, reflectedAngle_sub_add_pi_div_two,
    reflectedAngle_add_pi_div_two, reflectedAngle_coe, Set.inter_comm]
  congr 2
  congr 1
  ring_nf

/-- The preimage and image of a set agree under the involutive cap reflection. -/
theorem capReflection_preimage_eq_image (ω : ℝ) (S : Set Point) :
    capReflection ω ⁻¹' S = capReflection ω '' S := by
  ext p
  constructor
  · intro hp
    exact ⟨capReflection ω p, hp, capReflection_involutive ω p⟩
  · rintro ⟨q, hq, rfl⟩
    simpa only [Set.mem_preimage, capReflection_involutive] using hq

/-- The cap reflection preserves the real Lebesgue area of measurable sets. -/
theorem area_image_capReflection (ω : ℝ) (S : Set Point)
    (hS : MeasurableSet S) :
    ClassicalResults.area (capReflection ω '' S) = ClassicalResults.area S := by
  change (MeasureTheory.volume (capReflection ω '' S)).toReal =
    (MeasureTheory.volume S).toReal
  rw [← capReflection_preimage_eq_image]
  congr 1
  exact (LinearIsometryEquiv.measurePreserving (capReflection ω)).measure_preimage
    hS.nullMeasurableSet

/-- The vertical reflection of a body has mirrored support values. -/
theorem supportValue_reflectedBody_pi_div_two (K : ConvexBody Point) (u : ℝ) :
    supportValue (reflectedBody (Real.pi / 2) K : Set Point) (u : Real.Angle) =
      supportValue (K : Set Point) ((Real.pi - u : ℝ) : Real.Angle) := by
  have hang : ((Real.pi / 2 + Real.pi / 2 - u : ℝ) : Real.Angle) =
      ((Real.pi - u : ℝ) : Real.Angle) := by congr 1; ring
  rw [supportValue_reflectedBody, reflectedAngle_coe, hang]

/-- The vertical reflection mirrors normal projections. -/
theorem inner_capReflection_pi_div_two (p : Point) (u : ℝ) :
    inner ℝ (capReflection (Real.pi / 2) p) (normalVector (u : Real.Angle)) =
      inner ℝ p (normalVector ((Real.pi - u : ℝ) : Real.Angle)) := by
  have hang : ((Real.pi / 2 + Real.pi / 2 - u : ℝ) : Real.Angle) =
      ((Real.pi - u : ℝ) : Real.Angle) := by congr 1; ring
  rw [inner_capReflection_normalVector, reflectedAngle_coe, hang]
end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Support Intersections
-/

public section

noncomputable section

open Set MeasureTheory

namespace MovingSofa

private theorem supportingIntersection_le_supportValue_of_mem_Icc_left
    (K : ConvexBody Point) {a b r : ℝ} (hab : 0 < b - a) (hpi : b - a < Real.pi)
    (hr : r ∈ Set.Icc (a - Real.pi) a) :
    inner ℝ (supportingIntersection K (a : Real.Angle) (b : Real.Angle))
        (normalVector (r : Real.Angle)) ≤ supportValue K (r : Real.Angle) := by
  let p := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  let q := (edgeVertices K (a : Real.Angle)).1
  have hsin : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi hab hpi
  have hpa : inner ℝ p (normalVector (a : Real.Angle)) =
      supportValue K (a : Real.Angle) := supportingIntersection_inner_left K a b
  have hpb : inner ℝ p (normalVector (b : Real.Angle)) =
      supportValue K (b : Real.Angle) :=
    supportingIntersection_inner_right K a b hsin.ne'
  have hqmem := edgeVertices_fst_mem K (a : Real.Angle)
  have hqa : inner ℝ q (normalVector (a : Real.Angle)) =
      supportValue K (a : Real.Angle) := hqmem.2
  have hqb : inner ℝ q (normalVector (b : Real.Angle)) ≤
      supportValue K (b : Real.Angle) := inner_le_supportValue K hqmem.1 _
  have hnormal : inner ℝ (p - q) (normalVector (a : Real.Angle)) = 0 := by
    rw [inner_sub_left, hpa, hqa, sub_self]
  have htangent : 0 ≤ inner ℝ (p - q) (tangentVector (a : Real.Angle)) := by
    have hdiff : 0 ≤ inner ℝ (p - q) (normalVector (b : Real.Angle)) := by
      rw [inner_sub_left, hpb]
      linarith
    have hnb : normalVector (b : Real.Angle) =
        Real.cos (b - a) • normalVector (a : Real.Angle) +
          Real.sin (b - a) • tangentVector (a : Real.Angle) := by
      simpa only [add_sub_cancel] using normalVector_add_real a (b - a)
    rw [hnb, inner_add_right, inner_smul_right, inner_smul_right, hnormal,
      mul_zero, zero_add] at hdiff
    nlinarith
  have hqr : inner ℝ q (normalVector (r : Real.Angle)) ≤
      supportValue K (r : Real.Angle) := inner_le_supportValue K hqmem.1 _
  have hnr : normalVector (r : Real.Angle) =
      Real.cos (r - a) • normalVector (a : Real.Angle) +
        Real.sin (r - a) • tangentVector (a : Real.Angle) := by
    simpa only [add_sub_cancel] using normalVector_add_real a (r - a)
  have hsinr : Real.sin (r - a) ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith [hr.2]) (by linarith [hr.1])
  have hdiff : inner ℝ (p - q) (normalVector (r : Real.Angle)) ≤ 0 := by
    rw [hnr, inner_add_right, inner_smul_right, inner_smul_right, hnormal,
      mul_zero, zero_add]
    exact mul_nonpos_of_nonpos_of_nonneg hsinr htangent
  rw [inner_sub_left] at hdiff
  linarith

private theorem supportingIntersection_le_supportValue_of_mem_Icc_right
    (K : ConvexBody Point) {a b r : ℝ} (hab : 0 < b - a) (hpi : b - a < Real.pi)
    (hr : r ∈ Set.Icc b (b + Real.pi)) :
    inner ℝ (supportingIntersection K (a : Real.Angle) (b : Real.Angle))
        (normalVector (r : Real.Angle)) ≤ supportValue K (r : Real.Angle) := by
  let p := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  let q := (edgeVertices K (b : Real.Angle)).2
  have hsin : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi hab hpi
  have hsina : Real.sin (a - b) < 0 := by
    rw [show a - b = -(b - a) by ring, Real.sin_neg]
    exact neg_neg_of_pos hsin
  have hpa : inner ℝ p (normalVector (a : Real.Angle)) =
      supportValue K (a : Real.Angle) := supportingIntersection_inner_left K a b
  have hpb : inner ℝ p (normalVector (b : Real.Angle)) =
      supportValue K (b : Real.Angle) :=
    supportingIntersection_inner_right K a b hsin.ne'
  have hqmem := edgeVertices_snd_mem K (b : Real.Angle)
  have hqb : inner ℝ q (normalVector (b : Real.Angle)) =
      supportValue K (b : Real.Angle) := hqmem.2
  have hqa : inner ℝ q (normalVector (a : Real.Angle)) ≤
      supportValue K (a : Real.Angle) := inner_le_supportValue K hqmem.1 _
  have hnormal : inner ℝ (p - q) (normalVector (b : Real.Angle)) = 0 := by
    rw [inner_sub_left, hpb, hqb, sub_self]
  have htangent : inner ℝ (p - q) (tangentVector (b : Real.Angle)) ≤ 0 := by
    have hdiff : 0 ≤ inner ℝ (p - q) (normalVector (a : Real.Angle)) := by
      rw [inner_sub_left, hpa]
      linarith
    have hna : normalVector (a : Real.Angle) =
        Real.cos (a - b) • normalVector (b : Real.Angle) +
          Real.sin (a - b) • tangentVector (b : Real.Angle) := by
      simpa only [add_sub_cancel] using normalVector_add_real b (a - b)
    rw [hna, inner_add_right, inner_smul_right, inner_smul_right, hnormal,
      mul_zero, zero_add] at hdiff
    nlinarith
  have hqr : inner ℝ q (normalVector (r : Real.Angle)) ≤
      supportValue K (r : Real.Angle) := inner_le_supportValue K hqmem.1 _
  have hnr : normalVector (r : Real.Angle) =
      Real.cos (r - b) • normalVector (b : Real.Angle) +
        Real.sin (r - b) • tangentVector (b : Real.Angle) := by
    simpa only [add_sub_cancel] using normalVector_add_real b (r - b)
  have hsinr : 0 ≤ Real.sin (r - b) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hr.1]) (by linarith [hr.2])
  have hdiff : inner ℝ (p - q) (normalVector (r : Real.Angle)) ≤ 0 := by
    rw [hnr, inner_add_right, inner_smul_right, inner_smul_right, hnormal,
      mul_zero, zero_add]
    exact mul_nonpos_of_nonneg_of_nonpos hsinr htangent
  rw [inner_sub_left] at hdiff
  linarith

/-- Adjacent allowed support normals meet in the represented convex body. -/
theorem HasHalfPlaneRepresentation.supportingIntersection_mem_of_gap
    (K : ConvexBody Point) (R : Set ℝ) {a b : ℝ}
    (hab : 0 < b - a) (hpi : b - a < Real.pi)
    (hK : HasHalfPlaneRepresentation K ((fun r : ℝ ↦ (r : Real.Angle)) '' R))
    (hR : ∀ r ∈ R, r ∈ Set.Icc (a - Real.pi) a ∨ r ∈ Set.Icc b (b + Real.pi)) :
    supportingIntersection K (a : Real.Angle) (b : Real.Angle) ∈ K := by
  change supportingIntersection K (a : Real.Angle) (b : Real.Angle) ∈ (K : Set Point)
  rw [hK.eq_iInter_supportValue]
  simp only [Set.mem_iInter]
  intro u hu
  obtain ⟨r, hr, rfl⟩ := hu
  rcases hR r hr with hr | hr
  · exact supportingIntersection_le_supportValue_of_mem_Icc_left K hab hpi hr
  · exact supportingIntersection_le_supportValue_of_mem_Icc_right K hab hpi hr

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Top Corner
-/

public section

noncomputable section

namespace MovingSofa

/-- Every polygon cap of angle less than pi/2 contains the top parallelogram corner. -/
theorem stripParallelogram_top_mem_of_angle_lt (Θ : AngleSet)
    (hΘ : Θ.angle < Real.pi / 2) (K : PolygonCapSpace Θ) :
    (stripParallelogram Θ.angle).2.2 ∈ (K.val.val : Set Point) := by
  let o := (stripParallelogram Θ.angle).2.2
  have hc : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Θ.angle_pos, Real.pi_pos], hΘ⟩
  obtain ⟨pω, hpω, hpωeq⟩ := (K.val.val.isCompact.image
    (continuous_inner.comp (continuous_id.prodMk continuous_const))).sSup_mem
      (K.val.val.nonempty.image (fun p ↦ inner ℝ p (normalVector (Θ.angle : Real.Angle))))
  obtain ⟨pT, hpT, hpTeq⟩ := (K.val.val.isCompact.image
    (continuous_inner.comp (continuous_id.prodMk continuous_const))).sSup_mem
      (K.val.val.nonempty.image
        (fun p ↦ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))))
  have hpω' : inner ℝ pω (normalVector (Θ.angle : Real.Angle)) = 1 := by
    change inner ℝ pω (normalVector (Θ.angle : Real.Angle)) =
      supportValue K.val.val (Θ.angle : Real.Angle) at hpωeq
    simpa only [K.val.property.2.2.1] using hpωeq
  have hpT' : inner ℝ pT (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1 := by
    change inner ℝ pT (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue K.val.val ((Real.pi / 2 : ℝ) : Real.Angle) at hpTeq
    simpa only [K.val.property.2.2.2.1] using hpTeq
  have hpωT : inner ℝ pω (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤ 1 := by
    exact (inner_le_supportValue K.val.val hpω _).trans_eq K.val.property.2.2.2.1
  have hpTω : inner ℝ pT (normalVector (Θ.angle : Real.Angle)) ≤ 1 := by
    exact (inner_le_supportValue K.val.val hpT _).trans_eq K.val.property.2.2.1
  have hoω : inner ℝ o (normalVector (Θ.angle : Real.Angle)) = 1 := by
    have hgap : Real.tan (Real.pi / 4 - Θ.angle / 2) =
        (Real.cos Θ.angle)⁻¹ - Real.tan Θ.angle := by
      simpa [show Real.pi / 4 - Θ.angle / 2 =
          (Real.pi / 2 - Θ.angle) / 2 by ring]
        using Real.tan_pi_div_two_sub_div_two Θ.angle ⟨Θ.angle_pos.le, hΘ⟩
    have htan := Real.tan_eq_sin_div_cos Θ.angle
    simp [o, stripParallelogram, normalVector, frame, PiLp.inner_apply, hgap, htan]
    field_simp [hc.ne']
    ring
  have hoT : inner ℝ o (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1 := by
    simp [o, stripParallelogram, normalVector, frame, PiLp.inner_apply]
  rw [K.property.eq_iInter_supportValue]
  simp only [Set.mem_iInter]
  intro a ha
  change inner ℝ o (normalVector a) ≤ supportValue K.val.val a
  rcases ha with ⟨t, ht, rfl⟩ | ha
  · have htupper : t ∈ capUpperAngles Θ.angle := by
      rcases ht with (ht | ⟨s, hs, rfl⟩) | ht
      · exact Or.inl ⟨(Θ.interior t ht).1.le, (Θ.interior t ht).2.le⟩
      · exact Or.inr ⟨by dsimp; linarith [(Θ.interior s hs).1],
          by dsimp; linarith [(Θ.interior s hs).2]⟩
      · rcases ht with rfl | rfl
        · exact Or.inl ⟨Θ.angle_pos.le, le_rfl⟩
        · exact Or.inr ⟨le_rfl, by linarith [Θ.angle_pos]⟩
    rcases htupper with ht | ht
    · let c := Real.cos t / Real.cos Θ.angle
      let s := Real.sin (Θ.angle - t) / Real.cos Θ.angle
      have hc0 : 0 ≤ c := div_nonneg
        (Real.cos_nonneg_of_mem_Icc
          ⟨(neg_nonpos.mpr (by positivity)).trans ht.1, ht.2.trans Θ.angle_le⟩) hc.le
      have hs0 : 0 ≤ s := div_nonneg
        (Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr ht.2)
          (by linarith [ht.1, Θ.angle_le, Real.pi_pos])) hc.le
      have hdecomp : normalVector (t : Real.Angle) =
          c • normalVector (Θ.angle : Real.Angle) -
            s • normalVector ((Real.pi / 2 : ℝ) : Real.Angle) := by
        ext i
        fin_cases i
        · simp [c, s, normalVector, frame, Real.sin_sub]
          field_simp [hc.ne']
        · simp [c, s, normalVector, frame, Real.sin_sub]
          field_simp [hc.ne']
          ring
      rw [hdecomp, inner_sub_right, inner_smul_right, inner_smul_right, hoω, hoT]
      apply (inner_le_supportValue K.val.val hpω (t : Real.Angle)).trans'
      rw [hdecomp, inner_sub_right, inner_smul_right, inner_smul_right, hpω']
      simpa only [mul_one] using
        sub_le_sub_left (mul_le_mul_of_nonneg_left hpωT hs0) c
    · let c := Real.sin (t - Θ.angle) / Real.cos Θ.angle
      let s := -Real.cos t / Real.cos Θ.angle
      have hc0 : 0 ≤ c := div_nonneg
        (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1, Θ.angle_le])
          (by linarith [ht.2, Θ.angle_pos, Real.pi_pos])) hc.le
      have hs0 : 0 ≤ s := div_nonneg
        (neg_nonneg.mpr (Real.cos_nonpos_of_pi_div_two_le_of_le ht.1
          (by linarith [ht.2, Θ.angle_le, Real.pi_pos]))) hc.le
      have hdecomp : normalVector (t : Real.Angle) =
          c • normalVector ((Real.pi / 2 : ℝ) : Real.Angle) -
            s • normalVector (Θ.angle : Real.Angle) := by
        ext i
        fin_cases i
        · simp [c, s, normalVector, frame, Real.sin_sub]
          field_simp [hc.ne']
        · simp [c, s, normalVector, frame, Real.sin_sub]
          field_simp [hc.ne']
          ring
      rw [hdecomp, inner_sub_right, inner_smul_right, inner_smul_right, hoT, hoω]
      apply (inner_le_supportValue K.val.val hpT (t : Real.Angle)).trans'
      rw [hdecomp, inner_sub_right, inner_smul_right, inner_smul_right, hpT']
      simpa only [mul_one] using
        sub_le_sub_left (mul_le_mul_of_nonneg_left hpTω hs0) c
  · rcases ha with rfl | rfl
    · rw [normalVector_add_pi, inner_neg_right, hoω, K.val.property.2.2.2.2.1]
      norm_num
    · rw [inner_normalVector_three_pi_div_two, K.val.property.2.2.2.2.2.1]
      simp [o, stripParallelogram]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Vertical
-/

public section

noncomputable section

namespace MovingSofa

/-- A cap is closed under downward vertical movement that remains inside its fan. -/
theorem CapSpace.mem_of_fst_eq_of_snd_le {ω : ℝ} (K : CapSpace ω)
    {p q : Point} (hp : p ∈ (K.val : Set Point)) (hq : q ∈ capFan ω)
    (hx : q 0 = p 0) (hy : q 1 ≤ p 1) : q ∈ (K.val : Set Point) := by
  apply K.mem_of_mem_capFan_of_le_supportValue hq
  intro t ht
  apply le_trans _ (inner_le_supportValue K.val hp (t : Real.Angle))
  have htI : t ∈ Set.Icc 0 Real.pi := by
    rcases ht with ht | ht
    · exact ⟨ht.1, by linarith [ht.2, K.property.2.1, Real.pi_pos]⟩
    · exact ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, K.property.2.1]⟩
  have h := mul_le_mul_of_nonneg_left hy (Real.sin_nonneg_of_mem_Icc htI)
  simp [normalVector, frame, PiLp.inner_apply, hx]
  linarith

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Analysis.SurfaceMeasure.ArcConvergence`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Arc Convergence
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology BoundedContinuousFunction

namespace MovingSofa

/-- Hausdorff convergence with fixed endpoint atoms preserves half-open surface integrals. -/
theorem tendsto_integral_surfaceAreaMeasure_Ioc_of_fixed_atoms
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point) (L : Set Point))
      atTop (𝓝 0)) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (ha : ∀ n, surfaceAreaMeasure (K n) {(a : Real.Angle)} =
      surfaceAreaMeasure L {(a : Real.Angle)})
    (hb : ∀ n, surfaceAreaMeasure (K n) {(b : Real.Angle)} =
      surfaceAreaMeasure L {(b : Real.Angle)})
    (f : Real.Angle → ℝ) (hf : Continuous f) :
    Tendsto (fun n ↦ ∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc a b,
      f u ∂surfaceAreaMeasure (K n)) atTop
      (𝓝 (∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc a b, f u ∂surfaceAreaMeasure L)) := by
  let μs : ℕ → FiniteMeasure Real.Angle := fun n ↦
    ⟨surfaceAreaMeasure (K n), (surfaceAreaMeasure_face_union (K n)).1⟩
  let μ : FiniteMeasure Real.Angle :=
    ⟨surfaceAreaMeasure L, (surfaceAreaMeasure_face_union L).1⟩
  have hμ : Tendsto μs atTop (𝓝 μ) := by
    apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro g
    exact surfaceAreaMeasure_weak_continuity K L hlim g g.continuous
  exact Real.Angle.tendsto_integral_image_Ioc_of_fixed_endpoint_atoms
    hab hturn hμ ha hb (BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩)

/-- Preserving the two endpoint faces supplies the atomic hypotheses for arc convergence. -/
theorem tendsto_integral_surfaceAreaMeasure_Ioc_of_preserves_faces
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point) (L : Set Point))
      atTop (𝓝 0)) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (ha : ∀ n, exposedEdge (K n) (a : Real.Angle) = exposedEdge L (a : Real.Angle))
    (hb : ∀ n, exposedEdge (K n) (b : Real.Angle) = exposedEdge L (b : Real.Angle))
    (f : Real.Angle → ℝ) (hf : Continuous f) :
    Tendsto (fun n ↦ ∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc a b,
      f u ∂surfaceAreaMeasure (K n)) atTop
      (𝓝 (∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc a b, f u ∂surfaceAreaMeasure L)) := by
  apply tendsto_integral_surfaceAreaMeasure_Ioc_of_fixed_atoms K L hlim hab hturn
    (f := f) (hf := hf)
  · intro n
    rw [(surfaceAreaMeasure_atom_length (K n) _).1,
      (surfaceAreaMeasure_atom_length L _).1, ha n]
  · intro n
    rw [(surfaceAreaMeasure_atom_length (K n) _).1,
      (surfaceAreaMeasure_atom_length L _).1, hb n]

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Convex.CurveCut`.
* `Convex.ArcCutArea`.
* `Convex.OuterCornerPath`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Curve Cut
-/

public section

noncomputable section

namespace MovingSofa

private theorem normalVector_eq_positive_combo {a b t : ℝ}
    (hab : a < b) (hba : b < a + Real.pi) (_hat : a < t) (_htb : t < b) :
    normalVector (t : Real.Angle) =
      (Real.sin (b - t) / Real.sin (b - a)) • normalVector (a : Real.Angle) +
        (Real.sin (t - a) / Real.sin (b - a)) • normalVector (b : Real.Angle) := by
  have hs : Real.sin (b - a) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith)).ne'
  have hs' : Real.sin b * Real.cos a - Real.cos b * Real.sin a ≠ 0 := by
    simpa only [Real.sin_sub] using hs
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [normalVector, frame, Real.sin_sub] <;>
    field_simp [hs'] <;> ring

private theorem eq_supportingIntersection_of_mem_endpoint_faces
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (p : Point) (hpa : p ∈ exposedEdge K (a : Real.Angle))
    (hpb : p ∈ exposedEdge K (b : Real.Angle)) :
    supportingIntersection K a b = p := by
  let O := supportingIntersection K a b
  have hs : Real.sin (b - a) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith)).ne'
  have hna : inner ℝ (O - p) (normalVector (a : Real.Angle)) = 0 := by
    rw [inner_sub_left, supportingIntersection_inner_left, hpa.2, sub_self]
  have hnb : inner ℝ (O - p) (normalVector (b : Real.Angle)) = 0 := by
    rw [inner_sub_left, supportingIntersection_inner_right K a b hs, hpb.2, sub_self]
  have hrot := normalVector_add_real a (b - a)
  have htan : inner ℝ (O - p) (tangentVector (a : Real.Angle)) = 0 := by
    have := hnb
    rw [show normalVector (b : Real.Angle) =
      Real.cos (b - a) • normalVector (a : Real.Angle) +
        Real.sin (b - a) • tangentVector (a : Real.Angle) by
          simpa only [add_sub_cancel] using hrot,
      inner_add_right, inner_smul_right, inner_smul_right, hna] at this
    simp only [mul_zero, zero_add] at this
    exact (mul_eq_zero.mp this).resolve_left hs
  change O = p
  rw [show O = p + (O - p) by abel,
    ← inner_normalVector_smul_add_inner_tangentVector_smul
      (O - p) (a : Real.Angle), hna, htan, zero_smul, zero_smul, add_zero, add_zero]

private theorem exposedEdge_eq_singleton_of_common_endpoint
    (K : ConvexBody Point) {a b t : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hat : a < t) (htb : t < b) (p : Point)
    (hpa : p ∈ exposedEdge K (a : Real.Angle))
    (hpb : p ∈ exposedEdge K (b : Real.Angle)) :
    exposedEdge K (t : Real.Angle) = {p} := by
  have hsa : 0 < Real.sin (b - t) / Real.sin (b - a) := div_pos
    (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr htb) (by linarith))
    (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith))
  have hsb : 0 < Real.sin (t - a) / Real.sin (b - a) := div_pos
    (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hat) (by linarith))
    (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith))
  have hn := normalVector_eq_positive_combo hab hba hat htb
  have hpt : inner ℝ p (normalVector (t : Real.Angle)) = supportValue K t := by
    rw [hn, inner_add_right, inner_smul_right, inner_smul_right, hpa.2, hpb.2]
    apply le_antisymm
    · have hp_le := inner_le_supportValue K hpa.1 (t : Real.Angle)
      rw [hn, inner_add_right, inner_smul_right, inner_smul_right,
        hpa.2, hpb.2] at hp_le
      exact hp_le
    · apply csSup_le (K.nonempty.image _)
      rintro _ ⟨z, hzK, rfl⟩
      change inner ℝ z (normalVector (t : Real.Angle)) ≤ _
      rw [hn, inner_add_right, inner_smul_right, inner_smul_right]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (inner_le_supportValue K hzK _) hsa.le)
        (mul_le_mul_of_nonneg_left (inner_le_supportValue K hzK _) hsb.le)
  apply Set.Subset.antisymm
  · intro z hz
    have hza := inner_le_supportValue K hz.1 (a : Real.Angle)
    have hzb := inner_le_supportValue K hz.1 (b : Real.Angle)
    have hzt := hz.2
    change inner ℝ z (normalVector (t : Real.Angle)) = supportValue K t at hzt
    rw [← hpt, hn, inner_add_right, inner_smul_right, inner_smul_right] at hzt
    rw [inner_add_right, inner_smul_right, inner_smul_right, hpa.2, hpb.2] at hzt
    have hzea : inner ℝ z (normalVector (a : Real.Angle)) = supportValue K a := by
      by_contra hne
      have hlt := lt_of_le_of_ne hza hne
      nlinarith
    have hzeb : inner ℝ z (normalVector (b : Real.Angle)) = supportValue K b := by
      by_contra hne
      have hlt := lt_of_le_of_ne hzb hne
      nlinarith
    have hzpa : inner ℝ (z - p) (normalVector (a : Real.Angle)) = 0 := by
      rw [inner_sub_left, hzea, hpa.2, sub_self]
    have hzpb : inner ℝ (z - p) (normalVector (b : Real.Angle)) = 0 := by
      rw [inner_sub_left, hzeb, hpb.2, sub_self]
    have hs : Real.sin (b - a) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith)).ne'
    have htan : inner ℝ (z - p) (tangentVector (a : Real.Angle)) = 0 := by
      have hrot := normalVector_add_real a (b - a)
      rw [show normalVector (b : Real.Angle) =
        Real.cos (b - a) • normalVector (a : Real.Angle) +
          Real.sin (b - a) • tangentVector (a : Real.Angle) by
            simpa only [add_sub_cancel] using hrot,
        inner_add_right, inner_smul_right, inner_smul_right, hzpa] at hzpb
      simp only [mul_zero, zero_add] at hzpb
      exact (mul_eq_zero.mp hzpb).resolve_left hs
    have hzp : z = p := by
      rw [show z = p + (z - p) by abel,
        ← inner_normalVector_smul_add_inner_tangentVector_smul
          (z - p) (a : Real.Angle), hzpa, htan,
        zero_smul, zero_smul, add_zero, add_zero]
    simp [hzp]
  · intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    exact ⟨hpa.1, hpt⟩

private theorem exists_cut_angle
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    ∃ t d : ℝ, a < t ∧ t < b ∧ 0 < d ∧
      (edgeVertices K (b : Real.Angle)).2 - (edgeVertices K (a : Real.Angle)).1 =
        d • tangentVector (t : Real.Angle) := by
  let P := (edgeVertices K (a : Real.Angle)).1
  let Q := (edgeVertices K (b : Real.Angle)).2
  let O := supportingIntersection K a b
  obtain ⟨α, hα, hOa⟩ := supportingIntersection_eq_fst_add_pos_tangent K hab hba hne
  obtain ⟨β, hβ, hOb⟩ := supportingIntersection_eq_snd_sub_pos_tangent K hab hba hne
  have hchord : Q - P = α • tangentVector (a : Real.Angle) +
      β • tangentVector (b : Real.Angle) := by
    change O = P + α • tangentVector (a : Real.Angle) at hOa
    change O = Q - β • tangentVector (b : Real.Angle) at hOb
    have hQO : Q = O + β • tangentVector (b : Real.Angle) := by
      rw [hOb]
      module
    rw [hQO, hOa]
    module
  let f : ℝ → ℝ := fun s ↦ inner ℝ (Q - P) (normalVector (s : Real.Angle))
  have hf : Continuous f := by
    dsimp only [f]
    rw [show (fun s : ℝ ↦ inner ℝ (Q - P) (normalVector (s : Real.Angle))) =
      fun s ↦ (Q - P) 0 * Real.cos s + (Q - P) 1 * Real.sin s by
        funext s
        simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
        ring]
    fun_prop
  have hsin : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith)
  have hfa : f a < 0 := by
    dsimp only [f]
    rw [hchord, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    simp only [tangentVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe, normalVector,
      PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Fin.isValue,
      Matrix.cons_val_zero, mul_neg, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have hid : -(Real.cos a * Real.sin b) + Real.sin a * Real.cos b =
        -Real.sin (b - a) := by rw [Real.sin_sub]; ring
    rw [hid]
    nlinarith
  have hfb : 0 < f b := by
    dsimp only [f]
    rw [hchord, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    simp only [tangentVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe, normalVector,
      PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Fin.isValue,
      Matrix.cons_val_zero, mul_neg, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have hid : -(Real.cos b * Real.sin a) + Real.sin b * Real.cos a =
        Real.sin (b - a) := by rw [Real.sin_sub]; ring
    rw [hid]
    nlinarith
  have hz : (0 : ℝ) ∈ Set.Icc (f a) (f b) := ⟨hfa.le, hfb.le⟩
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab.le hf.continuousOn hz
  have hat : a < t := lt_of_le_of_ne ht.1 fun h ↦ by subst t; linarith
  have htb : t < b := lt_of_le_of_ne ht.2 fun h ↦ by subst t; linarith
  let d := inner ℝ (Q - P) (tangentVector (t : Real.Angle))
  have hdecomp : Q - P = d • tangentVector (t : Real.Angle) := by
    rw [← inner_normalVector_smul_add_inner_tangentVector_smul
      (Q - P) (t : Real.Angle)]
    change inner ℝ (Q - P) (normalVector (t : Real.Angle)) = 0 at hft
    rw [hft, zero_smul, zero_add]
  have hd : 0 < d := by
    have hqa : inner ℝ (Q - P) (normalVector (a : Real.Angle)) < 0 := hfa
    rw [hdecomp, real_inner_smul_left] at hqa
    have hsinat : 0 < Real.sin (t - a) :=
      Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hat) (by linarith)
    have hinner : inner ℝ (tangentVector (t : Real.Angle))
        (normalVector (a : Real.Angle)) = -Real.sin (t - a) := by
      rw [real_inner_comm]
      have h := sin_sub_eq_neg_inner_normalVector_tangentVector
        (a : Real.Angle) (t : Real.Angle)
      change Real.sin (t - a) =
        -inner ℝ (normalVector (a : Real.Angle)) (tangentVector (t : Real.Angle)) at h
      have h' := h
      linarith
    rw [hinner] at hqa
    nlinarith
  exact ⟨t, d, hat, htb, hd, hdecomp⟩

private theorem mem_segment_of_mem_body_of_eq_cut_inner
    (K : ConvexBody Point) {a b t c d : ℝ} (hat : a < t) (htb : t < b)
    (hba : b < a + Real.pi)
    (P Q z : Point) (hP : P = (edgeVertices K (a : Real.Angle)).1)
    (hQ : Q = (edgeVertices K (b : Real.Angle)).2)
    (hd : 0 < d) (hdir : Q - P = d • tangentVector (t : Real.Angle))
    (hPc : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hzc : inner ℝ z (normalVector (t : Real.Angle)) = c) (hzK : z ∈ K) :
    z ∈ segment ℝ P Q := by
  let r := inner ℝ (z - P) (tangentVector (t : Real.Angle))
  have hnormal : inner ℝ (z - P) (normalVector (t : Real.Angle)) = 0 := by
    rw [inner_sub_left, hzc, hPc, sub_self]
  have hzrepr : z = P + r • tangentVector (t : Real.Angle) := by
    rw [show z = P + (z - P) by abel,
      ← inner_normalVector_smul_add_inner_tangentVector_smul
        (z - P) (t : Real.Angle), hnormal, zero_smul, zero_add]
  have hza := inner_le_supportValue K hzK (a : Real.Angle)
  have hPa : inner ℝ P (normalVector (a : Real.Angle)) = supportValue K a := by
    rw [hP]
    exact (edgeVertices_fst_mem K (a : Real.Angle)).2
  have hsinA : 0 < Real.sin (t - a) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hat) (by linarith)
  have hta : inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (a : Real.Angle)) = -Real.sin (t - a) := by
    rw [real_inner_comm]
    have h := sin_sub_eq_neg_inner_normalVector_tangentVector
      (a : Real.Angle) (t : Real.Angle)
    change Real.sin (t - a) =
      -inner ℝ (normalVector (a : Real.Angle)) (tangentVector (t : Real.Angle)) at h
    linarith
  have hr0 : 0 ≤ r := by
    rw [hzrepr, inner_add_left, real_inner_smul_left, hta, hPa] at hza
    nlinarith
  have hzb := inner_le_supportValue K hzK (b : Real.Angle)
  have hQb : inner ℝ Q (normalVector (b : Real.Angle)) = supportValue K b := by
    rw [hQ]
    exact (edgeVertices_snd_mem K (b : Real.Angle)).2
  have hsinB : 0 < Real.sin (b - t) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr htb) (by linarith)
  have htbinner : inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (b : Real.Angle)) = Real.sin (b - t) := by
    have h := sin_sub_eq_neg_inner_normalVector_tangentVector
      (b : Real.Angle) (t : Real.Angle)
    change Real.sin (t - b) =
      -inner ℝ (normalVector (b : Real.Angle)) (tangentVector (t : Real.Angle)) at h
    rw [real_inner_comm]
    rw [show t - b = -(b - t) by ring, Real.sin_neg] at h
    linarith
  have hQrepr : Q = P + d • tangentVector (t : Real.Angle) := by
    rw [show Q = P + (Q - P) by abel, hdir]
  have hrd : r ≤ d := by
    rw [hzrepr, inner_add_left, real_inner_smul_left, htbinner] at hzb
    have hQsupport := hQb
    rw [hQrepr, inner_add_left, real_inner_smul_left, htbinner] at hQsupport
    rw [← hQsupport] at hzb
    nlinarith
  rw [segment_eq_image']
  refine ⟨r / d, ⟨div_nonneg hr0 hd.le, (div_le_one hd).2 hrd⟩, ?_⟩
  rw [hdir]
  dsimp only
  rw [smul_smul]
  rw [div_mul_cancel₀ r hd.ne', hzrepr]

private theorem exposedEdge_subset_upper_cut
    (K : ConvexBody Point) {a b t c s : ℝ} (hat : a < t) (htb : t < b)
    (hba : b < a + Real.pi) (hs : s ∈ Set.Ioo a b)
    (P Q : Point) (hP : P = (edgeVertices K (a : Real.Angle)).1)
    (hQ : Q = (edgeVertices K (b : Real.Angle)).2)
    (hPc : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQc : inner ℝ Q (normalVector (t : Real.Angle)) = c) :
    exposedEdge K (s : Real.Angle) ⊆ normalHalfPlane (t : Real.Angle) c true false := by
  intro z hz
  change c ≤ inner ℝ z (normalVector (t : Real.Angle))
  by_cases hst : s = t
  · subst s
    have hp_le := inner_le_supportValue K (edgeVertices_fst_mem K (a : Real.Angle)).1
      (t : Real.Angle)
    rw [← hP, hPc, ← hz.2] at hp_le
    exact hp_le
  rcases lt_or_gt_of_ne hst with hst | hts
  · have hn := normalVector_eq_positive_combo hat (by linarith) hs.1 hst
    have hA : 0 < Real.sin (t - s) / Real.sin (t - a) := div_pos
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hst) (by linarith [hba, hs.1]))
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hat) (by linarith))
    have hB : 0 < Real.sin (s - a) / Real.sin (t - a) := div_pos
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hs.1) (by linarith))
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hat) (by linarith))
    by_contra hnot
    have hzt : inner ℝ z (normalVector (t : Real.Angle)) < c := lt_of_not_ge hnot
    have hza := inner_le_supportValue K hz.1 (a : Real.Angle)
    have hPa : inner ℝ P (normalVector (a : Real.Angle)) = supportValue K a := by
      rw [hP]; exact (edgeVertices_fst_mem K _).2
    have hpK : P ∈ K := by rw [hP]; exact (edgeVertices_fst_mem K _).1
    have hp_le := inner_le_supportValue K hpK (s : Real.Angle)
    rw [← hz.2, hn, inner_add_right, inner_smul_right, inner_smul_right,
      inner_add_right, inner_smul_right, inner_smul_right, hPa, hPc] at hp_le
    nlinarith
  · have hn := normalVector_eq_positive_combo htb (by linarith) hts hs.2
    have hA : 0 < Real.sin (b - s) / Real.sin (b - t) := div_pos
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hs.2) (by linarith))
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr htb) (by linarith))
    have hB : 0 < Real.sin (s - t) / Real.sin (b - t) := div_pos
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hts) (by linarith [hba, hat, hs.2]))
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr htb) (by linarith))
    by_contra hnot
    have hzt : inner ℝ z (normalVector (t : Real.Angle)) < c := lt_of_not_ge hnot
    have hzb := inner_le_supportValue K hz.1 (b : Real.Angle)
    have hQb : inner ℝ Q (normalVector (b : Real.Angle)) = supportValue K b := by
      rw [hQ]; exact (edgeVertices_snd_mem K _).2
    have hqK : Q ∈ K := by rw [hQ]; exact (edgeVertices_snd_mem K _).1
    have hq_le := inner_le_supportValue K hqK (s : Real.Angle)
    rw [← hz.2, hn, inner_add_right, inner_smul_right, inner_smul_right,
      inner_add_right, inner_smul_right, inner_smul_right, hQc, hQb] at hq_le
    nlinarith

private theorem not_collinear_of_inner_eq_eq_lt
    (P Q O n : Point) (hPQ : P ≠ Q)
    (hPQn : inner ℝ P n = inner ℝ Q n) (hO : inner ℝ P n < inner ℝ O n) :
    ¬Collinear ℝ ({P, Q, O} : Set Point) := by
  intro hcol
  obtain ⟨p₀, v, hv⟩ := (collinear_iff_exists_forall_eq_smul_vadd
    (k := ℝ) ({P, Q, O} : Set Point)).mp hcol
  obtain ⟨rP, hrP⟩ := hv P (by simp)
  obtain ⟨rQ, hrQ⟩ := hv Q (by simp)
  obtain ⟨rO, hrO⟩ := hv O (by simp)
  have hrne : rP ≠ rQ := by
    intro h
    apply hPQ
    rw [hrP, hrQ, h]
  have hvn : inner ℝ v n = 0 := by
    rw [hrP, hrQ, vadd_eq_add, vadd_eq_add, inner_add_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left] at hPQn
    have : (rP - rQ) * inner ℝ v n = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hrne)
  rw [hrP, hrO, vadd_eq_add, vadd_eq_add, inner_add_left, inner_add_left,
    real_inner_smul_left, real_inner_smul_left, hvn] at hO
  simp only [mul_zero, zero_add] at hO
  exact hO.false

private theorem exposedEdge_upper_cut_first (K K' : ConvexBody Point)
    (a b t c : ℝ) (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hsub : (K' : Set Point) ⊆ (K : Set Point))
    (hcut : ∀ z ∈ (K' : Set Point), c ≤ inner ℝ z (normalVector (t : Real.Angle)))
    (hPmem : (edgeVertices K (a : Real.Angle)).1 ∈ K')
    (hPc : inner ℝ (edgeVertices K (a : Real.Angle)).1
      (normalVector (t : Real.Angle)) = c) :
    exposedEdge K' (a : Real.Angle) =
      {(edgeVertices K (a : Real.Angle)).1} := by
  let P := (edgeVertices K (a : Real.Angle)).1
  have hsin : 0 < Real.sin (t - a) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hat) (by linarith)
  have hsupport : supportValue K' (a : Real.Angle) = supportValue K (a : Real.Angle) := by
    apply le_antisymm
    · apply csSup_le (K'.nonempty.image _)
      rintro _ ⟨z, hz, rfl⟩
      exact inner_le_supportValue K (hsub hz) (a : Real.Angle)
    · rw [← (edgeVertices_fst_mem K (a : Real.Angle)).2]
      exact inner_le_supportValue K' hPmem (a : Real.Angle)
  apply Set.Subset.antisymm
  · intro z hz
    have hzKedge : z ∈ exposedEdge K (a : Real.Angle) := by
      refine ⟨hsub hz.1, ?_⟩
      change inner ℝ z (normalVector (a : Real.Angle)) = supportValue K a
      rw [← hsupport]
      exact hz.2
    have hnormal : inner ℝ (z - P) (normalVector (a : Real.Angle)) = 0 := by
      rw [inner_sub_left, hzKedge.2]
      change supportValue K (a : Real.Angle) -
        inner ℝ (edgeVertices K (a : Real.Angle)).1
          (normalVector (a : Real.Angle)) = 0
      rw [(edgeVertices_fst_mem K (a : Real.Angle)).2, sub_self]
    have htangent : inner ℝ (z - P) (tangentVector (a : Real.Angle)) ≤ 0 := by
      rw [inner_sub_left, sub_nonpos]
      change inner ℝ z (tangentVector (a : Real.Angle)) ≤
        inner ℝ (edgeVertices K (a : Real.Angle)).1
          (tangentVector (a : Real.Angle))
      rw [inner_edgeVertices_fst_tangent]
      exact le_csSup ((isCompact_exposedEdge K (a : Real.Angle)).image
        (continuous_id.inner continuous_const) |>.bddAbove) ⟨z, hzKedge, rfl⟩
    have hcut : 0 ≤ inner ℝ (z - P) (normalVector (t : Real.Angle)) := by
      rw [inner_sub_left, hPc]
      exact sub_nonneg.mpr (hcut z hz.1)
    have hrotate : normalVector (t : Real.Angle) =
        Real.cos (t - a) • normalVector (a : Real.Angle) +
          Real.sin (t - a) • tangentVector (a : Real.Angle) := by
      simpa only [add_sub_cancel] using normalVector_add_real a (t - a)
    rw [hrotate, inner_add_right, inner_smul_right, inner_smul_right, hnormal,
      mul_zero, zero_add] at hcut
    have htangent0 : inner ℝ (z - P) (tangentVector (a : Real.Angle)) = 0 := by
      nlinarith
    have hzP : z = P := by
      rw [show z = P + (z - P) by abel,
        ← inner_normalVector_smul_add_inner_tangentVector_smul
          (z - P) (a : Real.Angle), hnormal, htangent0,
        zero_smul, zero_smul, add_zero, add_zero]
    simp [hzP, P]
  · rintro z rfl
    refine ⟨hPmem, ?_⟩
    change inner ℝ P (normalVector (a : Real.Angle)) = supportValue K' a
    rw [hsupport]
    exact (edgeVertices_fst_mem K (a : Real.Angle)).2

private theorem exposedEdge_upper_cut_last (K K' : ConvexBody Point)
    (a b t c : ℝ) (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hsub : (K' : Set Point) ⊆ (K : Set Point))
    (hcut : ∀ z ∈ (K' : Set Point), c ≤ inner ℝ z (normalVector (t : Real.Angle)))
    (hQmem : (edgeVertices K (b : Real.Angle)).2 ∈ K')
    (hQc : inner ℝ (edgeVertices K (b : Real.Angle)).2
      (normalVector (t : Real.Angle)) = c) :
    exposedEdge K' (b : Real.Angle) =
      {(edgeVertices K (b : Real.Angle)).2} := by
  let Q := (edgeVertices K (b : Real.Angle)).2
  have hsupport : supportValue K' (b : Real.Angle) = supportValue K (b : Real.Angle) := by
    apply le_antisymm
    · apply csSup_le (K'.nonempty.image _)
      rintro _ ⟨z, hz, rfl⟩
      exact inner_le_supportValue K (hsub hz) (b : Real.Angle)
    · rw [← (edgeVertices_snd_mem K (b : Real.Angle)).2]
      exact inner_le_supportValue K' hQmem (b : Real.Angle)
  apply Set.Subset.antisymm
  · intro z hz
    have hzKedge : z ∈ exposedEdge K (b : Real.Angle) := by
      refine ⟨hsub hz.1, ?_⟩
      change inner ℝ z (normalVector (b : Real.Angle)) = supportValue K b
      rw [← hsupport]
      exact hz.2
    have hnormal : inner ℝ (z - Q) (normalVector (b : Real.Angle)) = 0 := by
      rw [inner_sub_left, hzKedge.2]
      change supportValue K (b : Real.Angle) -
        inner ℝ (edgeVertices K (b : Real.Angle)).2
          (normalVector (b : Real.Angle)) = 0
      rw [(edgeVertices_snd_mem K (b : Real.Angle)).2, sub_self]
    have htangent : 0 ≤ inner ℝ (z - Q) (tangentVector (b : Real.Angle)) := by
      rw [inner_sub_left, sub_nonneg]
      change inner ℝ (edgeVertices K (b : Real.Angle)).2
          (tangentVector (b : Real.Angle)) ≤
        inner ℝ z (tangentVector (b : Real.Angle))
      rw [inner_edgeVertices_snd_tangent]
      exact csInf_le ((isCompact_exposedEdge K (b : Real.Angle)).image
        (continuous_id.inner continuous_const) |>.bddBelow) ⟨z, hzKedge, rfl⟩
    have hcut : 0 ≤ inner ℝ (z - Q) (normalVector (t : Real.Angle)) := by
      rw [inner_sub_left, hQc]
      exact sub_nonneg.mpr (hcut z hz.1)
    have hrotate : normalVector (t : Real.Angle) =
        Real.cos (t - b) • normalVector (b : Real.Angle) +
          Real.sin (t - b) • tangentVector (b : Real.Angle) := by
      simpa only [add_sub_cancel] using normalVector_add_real b (t - b)
    have hsinb : Real.sin (t - b) < 0 := by
      rw [show t - b = -(b - t) by ring, Real.sin_neg, neg_lt_zero]
      exact Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr htb) (by linarith)
    rw [hrotate, inner_add_right, inner_smul_right, inner_smul_right, hnormal,
      mul_zero, zero_add] at hcut
    have htangent0 : inner ℝ (z - Q) (tangentVector (b : Real.Angle)) = 0 := by
      nlinarith
    have hzQ : z = Q := by
      rw [show z = Q + (z - Q) by abel,
        ← inner_normalVector_smul_add_inner_tangentVector_smul
          (z - Q) (b : Real.Angle), hnormal, htangent0,
        zero_smul, zero_smul, add_zero, add_zero]
    simp [hzQ, Q]
  · rintro z rfl
    refine ⟨hQmem, ?_⟩
    change inner ℝ Q (normalVector (b : Real.Angle)) = supportValue K' b
    rw [hsupport]
    exact (edgeVertices_snd_mem K (b : Real.Angle)).2

theorem convexBoundaryArc_cut (K : ConvexBody Point) (a b : ℝ)
    (hab : a < b) (hba : b < a + Real.pi)
    (P Q O : Point) (hP : P = (edgeVertices K a).1)
    (hQ : Q = (edgeVertices K b).2) (hO : O = supportingIntersection K a b) :
    (P = Q → O = P ∧ convexBoundaryArc K a b = {P}) ∧
    (P ≠ Q → ¬ Collinear ℝ ({P, Q, O} : Set Point) ∧
      ∃ (t c : ℝ) (K' : ConvexBody Point),
        a < t ∧ t < b ∧
        inner ℝ P (normalVector (t : Real.Angle)) = c ∧
        inner ℝ Q (normalVector (t : Real.Angle)) = c ∧
        c < inner ℝ O (normalVector (t : Real.Angle)) ∧
        (K' : Set Point) = (K : Set Point) ∩ normalHalfPlane t c true false ∧
        (∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K' s = {P}) ∧
        (∀ s ∈ Set.Ioo a b, exposedEdge K' s = exposedEdge K s) ∧
        (∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K' s = {Q}) ∧
        exposedEdge K' (t + Real.pi) = segment ℝ Q P) := by
  subst P
  subst Q
  subst O
  constructor
  · intro hPQ
    have hPa := edgeVertices_fst_mem K (a : Real.Angle)
    have hPb : (edgeVertices K (a : Real.Angle)).1 ∈ exposedEdge K (b : Real.Angle) := by
      rw [hPQ]
      exact edgeVertices_snd_mem K (b : Real.Angle)
    have hO := eq_supportingIntersection_of_mem_endpoint_faces K hab hba
      (edgeVertices K (a : Real.Angle)).1 hPa hPb
    refine ⟨hO, ?_⟩
    have hfaces : ∀ t ∈ Set.Ioo a b, exposedEdge K (t : Real.Angle) =
        {(edgeVertices K (a : Real.Angle)).1} := by
      intro t ht
      exact exposedEdge_eq_singleton_of_common_endpoint K hab hba ht.1 ht.2 _ hPa hPb
    rw [convexBoundaryArc, hPQ]
    apply Set.Subset.antisymm
    · refine Set.union_subset (Set.union_subset (Set.Subset.rfl) ?_) Set.Subset.rfl
      exact Set.iUnion₂_subset fun t ht ↦ by simpa [← hPQ] using (hfaces t ht).le
    · exact Set.subset_union_left.trans Set.subset_union_left
  · intro hPQ
    let P := (edgeVertices K (a : Real.Angle)).1
    let Q := (edgeVertices K (b : Real.Angle)).2
    let O := supportingIntersection K a b
    obtain ⟨t, d, hat, htb, hd, hdir⟩ := exists_cut_angle K hab hba hPQ
    let c := inner ℝ P (normalVector (t : Real.Angle))
    have hPc : inner ℝ P (normalVector (t : Real.Angle)) = c := rfl
    have hQc : inner ℝ Q (normalVector (t : Real.Angle)) = c := by
      have hdiff : inner ℝ (Q - P) (normalVector (t : Real.Angle)) = 0 := by
        rw [hdir, real_inner_smul_left, real_inner_comm,
          inner_normalVector_tangentVector, mul_zero]
      rw [inner_sub_left, hPc] at hdiff
      linarith
    have hPK : P ∈ K := edgeVertices_fst_mem K (a : Real.Angle) |>.1
    have hQK : Q ∈ K := edgeVertices_snd_mem K (b : Real.Angle) |>.1
    let K' : ConvexBody Point :=
      { carrier := (K : Set Point) ∩ normalHalfPlane (t : Real.Angle) c true false
        convex' := K.convex.inter (convex_normalHalfPlane _ _ true)
        isCompact' := K.isCompact.inter_right (isClosed_normalHalfPlane _ _ true)
        nonempty' := ⟨P, hPK, by change c ≤ _; exact hPc.ge⟩ }
    have hK' : (K' : Set Point) = (K : Set Point) ∩
        normalHalfPlane (t : Real.Angle) c true false := rfl
    obtain ⟨α, hα, hOa⟩ :=
      supportingIntersection_eq_fst_add_pos_tangent K hab hba hPQ
    have hsin : 0 < Real.sin (t - a) :=
      Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hat) (by linarith)
    have hta : inner ℝ (tangentVector (a : Real.Angle))
        (normalVector (t : Real.Angle)) = Real.sin (t - a) := by
      have h := sin_sub_eq_neg_inner_normalVector_tangentVector
        (t : Real.Angle) (a : Real.Angle)
      change Real.sin (a - t) =
        -inner ℝ (normalVector (t : Real.Angle)) (tangentVector (a : Real.Angle)) at h
      rw [real_inner_comm, show a - t = -(t - a) by ring, Real.sin_neg] at h
      linarith
    have hcO : c < inner ℝ O (normalVector (t : Real.Angle)) := by
      change O = P + α • tangentVector (a : Real.Angle) at hOa
      rw [hOa, inner_add_left, real_inner_smul_left, hta, ← hPc]
      nlinarith
    have hncol : ¬Collinear ℝ ({P, Q, O} : Set Point) :=
      not_collinear_of_inner_eq_eq_lt P Q O (normalVector (t : Real.Angle))
        hPQ (hPc.trans hQc.symm) hcO
    have hPmem : P ∈ K' := ⟨hPK, by change c ≤ _; exact hPc.ge⟩
    have hQmem : Q ∈ K' := ⟨hQK, by change c ≤ _; exact hQc.ge⟩
    have hsupportTerminal :
        supportValue K' ((t + Real.pi : ℝ) : Real.Angle) = -c := by
      apply le_antisymm
      · apply csSup_le (K'.nonempty.image _)
        rintro _ ⟨z, hz, rfl⟩
        have hzcut := hz.2
        change c ≤ inner ℝ z (normalVector (t : Real.Angle)) at hzcut
        rw [normalVector_add_pi]
        change inner ℝ z (-normalVector (t : Real.Angle)) ≤ -c
        rw [inner_neg_right]
        linarith
      · have hp := inner_le_supportValue K' hPmem ((t + Real.pi : ℝ) : Real.Angle)
        rw [normalVector_add_pi, inner_neg_right, hPc] at hp
        exact hp
    have haFace := exposedEdge_upper_cut_first K K' a b t c hat htb hba
      (fun _ hz ↦ hz.1) (fun _ hz ↦ hz.2) hPmem hPc
    have hbFace := exposedEdge_upper_cut_last K K' a b t c hat htb hba
      (fun _ hz ↦ hz.1) (fun _ hz ↦ hz.2) hQmem hQc
    have hangleTerminal :
        ((t - Real.pi : ℝ) : Real.Angle) = ((t + Real.pi : ℝ) : Real.Angle) := by
      rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub]
      refine ⟨-1, ?_⟩
      norm_num
      ring
    have hPterminalPlus : P ∈ exposedEdge K' ((t + Real.pi : ℝ) : Real.Angle) := by
      refine ⟨hPmem, ?_⟩
      change inner ℝ P (normalVector ((t + Real.pi : ℝ) : Real.Angle)) =
        supportValue K' ((t + Real.pi : ℝ) : Real.Angle)
      rw [normalVector_add_pi, inner_neg_right, hsupportTerminal, hPc]
    have hQterminalPlus : Q ∈ exposedEdge K' ((t + Real.pi : ℝ) : Real.Angle) := by
      refine ⟨hQmem, ?_⟩
      change inner ℝ Q (normalVector ((t + Real.pi : ℝ) : Real.Angle)) =
        supportValue K' ((t + Real.pi : ℝ) : Real.Angle)
      rw [normalVector_add_pi, inner_neg_right, hsupportTerminal, hQc]
    have hPterminalMinus : P ∈ exposedEdge K' ((t - Real.pi : ℝ) : Real.Angle) := by
      rw [hangleTerminal]
      exact hPterminalPlus
    refine ⟨hncol, t, c, K', hat, htb, hPc, hQc, hcO, hK', ?_, ?_, ?_, ?_⟩
    · intro s hs
      rcases eq_or_lt_of_le hs.2 with hsa | hsa
      · subst s
        exact haFace
      · exact exposedEdge_eq_singleton_of_common_endpoint K'
          (by linarith) (by linarith) hs.1 hsa P hPterminalMinus
          (by rw [haFace]; rfl)
    · intro s hs
      have hsub := exposedEdge_subset_upper_cut K hat htb hba hs P Q rfl rfl hPc hQc
      obtain ⟨z₀, hz₀⟩ := exposedEdge_nonempty K (s : Real.Angle)
      have hz₀K' : z₀ ∈ K' := ⟨hz₀.1, hsub hz₀⟩
      have hsupport : supportValue K' (s : Real.Angle) = supportValue K (s : Real.Angle) := by
        apply le_antisymm
        · apply csSup_le (K'.nonempty.image _)
          rintro _ ⟨z, hz, rfl⟩
          exact inner_le_supportValue K hz.1 (s : Real.Angle)
        · rw [← hz₀.2]
          exact inner_le_supportValue K' hz₀K' (s : Real.Angle)
      ext z
      constructor
      · intro hz
        refine ⟨hz.1.1, ?_⟩
        change inner ℝ z (normalVector (s : Real.Angle)) = supportValue K s
        rw [← hsupport]
        exact hz.2
      · intro hz
        refine ⟨⟨hz.1, hsub hz⟩, ?_⟩
        change inner ℝ z (normalVector (s : Real.Angle)) = supportValue K' s
        rw [hsupport]
        exact hz.2
    · intro s hs
      rcases eq_or_lt_of_le hs.1 with hbs | hbs
      · subst s
        exact hbFace
      · exact exposedEdge_eq_singleton_of_common_endpoint K'
          (by linarith) (by linarith) hbs hs.2 Q
          (by rw [hbFace]; rfl) hQterminalPlus
    · have hsupport := hsupportTerminal
      apply Set.Subset.antisymm
      · intro z hz
        have hzcut := hz.1.2
        change c ≤ inner ℝ z (normalVector (t : Real.Angle)) at hzcut
        have hzeq := hz.2
        change inner ℝ z (normalVector ((t + Real.pi : ℝ) : Real.Angle)) =
          supportValue K' ((t + Real.pi : ℝ) : Real.Angle) at hzeq
        rw [normalVector_add_pi, inner_neg_right, hsupport] at hzeq
        have hzc : inner ℝ z (normalVector (t : Real.Angle)) = c := by linarith
        rw [segment_symm ℝ]
        exact mem_segment_of_mem_body_of_eq_cut_inner K hat htb hba P Q z rfl rfl
          hd hdir hPc hzc hz.1.1
      · intro z hz
        have hzK : z ∈ K := K.convex.segment_subset hQK hPK hz
        have hzc : inner ℝ z (normalVector (t : Real.Angle)) = c := by
          have hlin := (convex_normalHalfPlane (t : Real.Angle) c true).segment_subset
            (show P ∈ normalHalfPlane (t : Real.Angle) c true false by
              change c ≤ _; exact hPc.ge)
            (show Q ∈ normalHalfPlane (t : Real.Angle) c true false by
              change c ≤ _; exact hQc.ge)
          have hzcut := hlin (show z ∈ segment ℝ P Q by simpa [segment_symm ℝ] using hz)
          rw [segment_eq_image'] at hz
          obtain ⟨u, hu, rfl⟩ := hz
          rw [inner_add_left, inner_smul_left, inner_sub_left, hPc, hQc]
          ring
        refine ⟨⟨hzK, by change c ≤ _; exact hzc.ge⟩, ?_⟩
        change inner ℝ z (normalVector ((t + Real.pi : ℝ) : Real.Angle)) =
          supportValue K' ((t + Real.pi : ℝ) : Real.Angle)
        rw [normalVector_add_pi, inner_neg_right, hsupport, hzc]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Arc Cut Area
-/

public section

noncomputable section

namespace MovingSofa

open Set

/-- A supporting chord of a convex-body frontier cuts off a rectifiable oriented arc, and the
closed signed area is the sum of the arc area and the oppositely oriented chord area. -/
theorem exists_rectifiableOrientedArc_of_cut_with_area
    (K : ConvexBody Point) {t c d α β : ℝ} {P Q : Point} {U : Set Point}
    {x : ContinuousBVPaths α β}
    (hαβ : α < β)
    (hx : IsOrientedJordanParametrization hαβ.le (frontier (K : Set Point)) true x.val)
    (hPQ : P ≠ Q) (hbase : x.val ⟨α, le_rfl, hαβ.le⟩ ∉ segment ℝ P Q)
    (hfrontier : frontier (K : Set Point) = U ∪ segment ℝ P Q)
    (hinter : U ∩ segment ℝ P Q = {P, Q})
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hterminal : exposedEdge K (t + Real.pi) = segment ℝ Q P)
    (hd : 0 < d) (hdir : Q - P = d • tangentVector (t : Real.Angle)) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = U ∧
      A.val.startPoint = P ∧ A.val.endPoint = Q ∧
      curveAreaFunctional x = jordanArcArea A + segmentArea Q P := by
  let θ : Real.Angle := (t + Real.pi : ℝ)
  have hhalf : frontier (K : Set Point) ⊆ normalHalfPlane θ (-c) false false := by
    intro z hz
    have hzK : z ∈ K := K.isClosed.frontier_subset hz
    have hzle := inner_le_supportValue K hzK θ
    have hPterm : P ∈ exposedEdge K θ := by
      rw [show exposedEdge K θ = segment ℝ Q P by
        simpa only [θ, Real.Angle.coe_add] using hterminal]
      exact right_mem_segment ℝ Q P
    have hsupp : supportValue K θ = -c := by
      have h := hPterm.2
      change inner ℝ P (normalVector θ) = supportValue K θ at h
      change inner ℝ P (normalVector (((t + Real.pi : ℝ) : Real.Angle))) = _ at h
      rw [normalVector_add_pi, inner_neg_right, hPt] at h
      linarith
    change inner ℝ z (normalVector θ) ≤ -c
    rwa [hsupp] at hzle
  have hQline : Q ∈ normalLine θ (-c) := by
    change inner ℝ Q (normalVector θ) = -c
    change inner ℝ Q (normalVector (((t + Real.pi : ℝ) : Real.Angle))) = -c
    rw [normalVector_add_pi, inner_neg_right, hQt]
  have hdir' : P = Q + d • tangentVector θ := by
    have htangent : tangentVector θ = -tangentVector (t : Real.Angle) := by
      ext i
      fin_cases i <;> simp [θ, tangentVector, frame]
    rw [htangent]
    calc
      P = Q - (Q - P) := by module
      _ = Q - d • tangentVector (t : Real.Angle) := by rw [hdir]
      _ = Q + d • -tangentVector (t : Real.Angle) := by module
  exact exists_rectifiableOrientedArc_of_supportingChord_with_area
    hαβ hx P Q hPQ
    hbase hfrontier hinter θ (-c) hhalf hQline d hd hdir'

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The outer corner of a convex body as a path of bounded variation

The outer corner of the rotating supporting hallway of a convex body `K` is
`h_K(t) • u_t + h_K(t + π/2) • v_t`.  Support values are Lipschitz in the angle and bounded on a
compact interval, so this expression is a Lipschitz, hence continuous bounded-variation, path on
every compact interval of angles; and it is convex-linear in `K` because support values are.
These are the two hypotheses of Mamikon convexity for the middle summand of the sofa area.
-/

public section

noncomputable section

open scoped unitInterval

namespace MovingSofa

/-- The outer corner of a convex body traces a continuous path of bounded variation over every
compact interval of angles. -/
theorem exists_outerCornerBV (K : ConvexBody Point) (a b : ℝ) :
    ∃ γ : ContinuousBVPaths a b, ∀ s : Set.Icc a b,
      γ.val s = (rotatingHallwayParts (K : Set Point) ((s : ℝ) : Real.Angle)).outerCorner := by
  set C := sSup (norm '' (K : Set Point))
  have hC0 : 0 ≤ C := Real.sSup_nonneg (by rintro _ ⟨p, -, rfl⟩; exact norm_nonneg p)
  have hlipn : ∀ x y : ℝ, |supportValue (K : Set Point) (x : Real.Angle) -
      supportValue (K : Set Point) (y : Real.Angle)| ≤ C * |x - y| :=
    abs_supportValue_sub_le_of_isCompact K.nonempty K.isCompact
  have hlipt : ∀ x y : ℝ,
      |supportValue (K : Set Point) ((x + Real.pi / 2 : ℝ) : Real.Angle) -
        supportValue (K : Set Point) ((y + Real.pi / 2 : ℝ) : Real.Angle)| ≤ C * |x - y| := by
    intro x y
    simpa only [add_sub_add_right_eq_sub] using hlipn (x + Real.pi / 2) (y + Real.pi / 2)
  have hcont : Continuous fun x : ℝ ↦
      supportValue (K : Set Point) ((x + Real.pi / 2 : ℝ) : Real.Angle) :=
    (continuous_supportValue_real K).comp (continuous_id.add_const _)
  obtain ⟨Mn, hMn⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc a b)
    (continuous_supportValue_real K).continuousOn
  obtain ⟨Mt, hMt⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc a b)
    hcont.continuousOn
  set M := max (max Mn Mt) 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hMn' : ∀ x ∈ Set.Icc a b, |supportValue (K : Set Point) (x : Real.Angle)| ≤ M := by
    intro x hx
    simpa only [Real.norm_eq_abs] using
      (hMn x hx).trans ((le_max_left Mn Mt).trans (le_max_left _ 0))
  have hMt' : ∀ x ∈ Set.Icc a b,
      |supportValue (K : Set Point) ((x + Real.pi / 2 : ℝ) : Real.Angle)| ≤ M := by
    intro x hx
    simpa only [Real.norm_eq_abs] using
      (hMt x hx).trans ((le_max_right Mn Mt).trans (le_max_left _ 0))
  exact ⟨continuousBVOfLipschitz _ (lipschitzOnWith_frameCombination
      (D := ⟨2 * (C + M), by linarith⟩) le_rfl hM0 hlipn hlipt hMn' hMt').to_restrict,
    fun s ↦ (outerCorner_eq_support_sum K (s : ℝ)).symm⟩

/-- The outer-corner paths of a convex body may be chosen convex-linearly in the body.  The
barycentric operation on paths is `bvPathCombination`, spelled out here because it is defined
downstream of this module. -/
theorem exists_outerCornerBV_convexLinear (a b : ℝ) :
    ∃ γ : ConvexBody Point → ContinuousBVPaths a b,
      (∀ (K : ConvexBody Point) (s : Set.Icc a b), (γ K).val s =
        (rotatingHallwayParts (K : Set Point) ((s : ℝ) : Real.Angle)).outerCorner) ∧
      IsConvexLinear convexBodyCombination
        (fun r x y ↦ (1 - (r : ℝ)) • x + (r : ℝ) • y) γ := by
  choose γ hγ using fun K : ConvexBody Point ↦ exists_outerCornerBV K a b
  refine ⟨γ, hγ, fun t K L ↦ Subtype.ext (funext fun s ↦ ?_)⟩
  change (γ (convexBodyCombination t K L)).val s =
    ((1 - (t : ℝ)) • (γ K).val + (t : ℝ) • (γ L).val) s
  rw [hγ, show ((1 - (t : ℝ)) • (γ K).val + (t : ℝ) • (γ L).val) s =
      (1 - (t : ℝ)) • (γ K).val s + (t : ℝ) • (γ L).val s from rfl, hγ, hγ]
  simp only [outerCorner_eq_support_sum, supportValue_convexBodyCombination]
  module

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Geometry.Convex.HorizontalExtrema`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Convex / Horizontal Extrema
-/

public section

noncomputable section

namespace MovingSofa

/-- A horizontal extreme slice is a singleton when every defining normal has nonzero sine. -/
lemma ConvexBody.eq_of_mem_of_fst_eq_of_fst_extremal
    (K : ConvexBody Point) (N : Set Real.Angle) (hN : N.Finite)
    (hK : HasHalfPlaneRepresentation K N) (hsin : ∀ t ∈ N, t.sin ≠ 0)
    {a b : Point} (ha : a ∈ (K : Set Point)) (hb : b ∈ (K : Set Point))
    (hab : a 0 = b 0)
    (hext : (∀ q ∈ (K : Set Point), q 0 ≤ a 0) ∨
      (∀ q ∈ (K : Set Point), a 0 ≤ q 0)) : a = b := by
  by_contra hne
  have hy : a 1 ≠ b 1 := by
    intro h
    apply hne
    ext i
    fin_cases i
    · exact hab
    · exact h
  let m : Point := (2 : ℝ)⁻¹ • (a + b)
  let U : Set Point := ⋂ t ∈ N,
    {q | inner ℝ q (normalVector t) < supportValue K t}
  have hU : IsOpen U := by
    apply hN.isOpen_biInter
    intro t ht
    exact isOpen_lt (by fun_prop) continuous_const
  have hm : m ∈ U := by
    simp only [U, Set.mem_iInter, Set.mem_ofPred_eq]
    intro t ht
    have ha' := inner_le_supportValue K ha t
    have hb' := inner_le_supportValue K hb t
    have hneq : inner ℝ a (normalVector t) ≠ inner ℝ b (normalVector t) := by
      intro heq
      have hdiff : t.sin * (a 1 - b 1) = 0 := by
        simp only [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] at heq
        simp only [Fin.isValue, Matrix.cons_val_zero, RCLike.inner_apply, conj_trivial,
          Matrix.cons_val_one, Matrix.cons_val_fin_one] at heq
        rw [hab] at heq
        nlinarith
      exact hy (sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left (hsin t ht)))
    have hmid : inner ℝ m (normalVector t) =
        (inner ℝ a (normalVector t) + inner ℝ b (normalVector t)) / 2 := by
      simp only [m, inner_add_left, real_inner_smul_left]
      ring
    rw [hmid]
    rcases lt_or_gt_of_ne hneq with h | h <;> linarith
  obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.mp hU) m hm
  have hmem (r : ℝ) (hr : |r| < ε) :
      m + r • normalVector (0 : Real.Angle) ∈ (K : Set Point) := by
    have hqm : m + r • normalVector (0 : Real.Angle) ∈ Metric.ball m ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [add_sub_cancel_left, norm_smul]
      have hn : ‖normalVector (0 : Real.Angle)‖ = 1 := by
        simpa only [Real.Angle.coe_zero] using norm_normalVector_real 0
      simpa only [hn, mul_one, Real.norm_eq_abs] using hr
    rw [hK.eq_iInter_supportValue]
    simp only [Set.mem_iInter]
    intro t ht
    have h := Set.mem_iInter.mp (Set.mem_iInter.mp (hball hqm) t) ht
    change inner ℝ (m + r • normalVector (0 : Real.Angle)) (normalVector t) <
      supportValue K t at h
    exact h.le
  have hcoord (r : ℝ) : (m + r • normalVector (0 : Real.Angle)) 0 = a 0 + r := by
    simp [m, normalVector, frame, ← hab]
    ring
  rcases hext with hmax | hmin
  · have hq := hmem (ε / 2) (by rw [abs_of_pos (half_pos hε)]; linarith)
    have h := hmax _ hq
    rw [hcoord] at h
    linarith
  · have hq := hmem (-ε / 2) (by rw [abs_of_neg (by linarith : -ε / 2 < 0)]; linarith)
    have h := hmin _ hq
    rw [hcoord] at h
    linarith

/-- Every horizontal coordinate between two points of a convex body is attained. -/
lemma ConvexBody.exists_mem_fst_eq_of_mem_Icc (K : ConvexBody Point) {a b : Point}
    (ha : a ∈ (K : Set Point)) (hb : b ∈ (K : Set Point)) (hab : a 0 < b 0)
    {x : ℝ} (hx : x ∈ Set.Icc (a 0) (b 0)) :
    ∃ q ∈ (K : Set Point), q 0 = x := by
  let r := (x - a 0) / (b 0 - a 0)
  have hd : 0 < b 0 - a 0 := sub_pos.mpr hab
  have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr hx.1) hd.le
  have hr1 : r ≤ 1 := by
    dsimp [r]
    rw [div_le_one hd]
    linarith [hx.2]
  refine ⟨(1 - r) • a + r • b,
    K.convex ha hb (sub_nonneg.mpr hr1) hr (by ring), ?_⟩
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  dsimp [r]
  field_simp
  ring

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Gerver.Motion`.
* `Gerver.PaperPath`.
* `Gerver.PaperSet`.
* `Gerver.Parameters`.
* `Gerver.ParameterDictionary`.
* `Gerver.Partition`.
* `Gerver.ReversePhysicalDomain`.
* `Gerver.DirectRegularity`.
* `Gerver.LiteralSets`.
* `Gerver.LiteralConnected`.
* `Gerver.ParameterIdentification`.
* `Gerver.Contacts`.
* `Gerver.Niche.Roof`.
* `Gerver.ODEs`.
* `Gerver.OuterContacts`.
* `Gerver.StageRegularity`.
* `Gerver.Area.Grid`.
* `Gerver.Niche.RoofProperties`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-
MIT License

Copyright (c) 2026 Dawid Trela

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/


/-! Adapted from GerverSofaLean v1.1.0, F07UpstreamMotion (MIT). -/

public section

noncomputable section
open MeasureTheory
open scoped unitInterval ENNReal

namespace MovingSofa

open GerverSofa.PartF

/-- The certified continuous rigid motion carrying Gerver’s sofa through the hallway. -/
def gerversSofaMotion : I → Rigid := EuclideanMotion.motion

theorem isMovingSofa_gerversSofa_motion : IsMovingSofa gerversSofa gerversSofaMotion := by
  apply (ProjectAdapter.isMovingSofa_iff_model _ _).2
  rw [ProjectAdapter.gerversSofa_eq_certified]
  exact EuclideanMotion.concrete_movingSofa

theorem isMovingSofa_gerversSofa : ∃ m, IsMovingSofa gerversSofa m :=
  ⟨gerversSofaMotion, isMovingSofa_gerversSofa_motion⟩

theorem volume_gerversSofa_le_sofaConstant : volume gerversSofa ≤ sofaConstant := by
  unfold sofaConstant
  exact le_iSup_of_le gerversSofa (le_iSup_of_le isMovingSofa_gerversSofa le_rfl)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The paper's Gerver path and the vendor coordinate transport

`paperGerverPath` is the certified direct five-phase Gerver path read through the vendor
coordinate identification `GerverSofa.PartF.Coordinates.toPlane`.  This file records the
transport lemmas for that identification (derivatives, smoothness, continuity) and the
frame readers that express the moving frame `normalVector`/`tangentVector` in the same
coordinates.

The frame readers live here rather than in `MovingSofa/Geometry/Basic.lean` because their
statements mention `toPlane`, which `Geometry/Basic.lean` does not import; this is the
lowest module that sees both the vendor coordinates and `MovingSofa.frame`.
-/

public section

noncomputable section

open scoped ContDiff

namespace MovingSofa

/-- The certified direct five-phase Gerver path, taking the earlier branch at each switch. -/
@[expose]
def paperGerverPath (t : ℝ) : Point :=
  GerverSofa.PartF.Coordinates.toPlane (GerverSofa.Romik.path GerverSofa.PartB.params t)

theorem canonical_path_rotation_eq_paper (t : ℝ) (ht : t ∈ Set.Icc 0 (Real.pi / 2)) :
    rotationMap (t : Real.Angle) (GerversSofa.p t) = paperGerverPath t :=
  GerverSofa.PartF.ProjectAdapter.integral_rotation_to_full t ht

section Transport

open GerverSofa.Romik GerverSofa.PartF.Coordinates

/-! ### Transport along the coordinate identification -/

/-- The coordinate identification `toPlane` is a continuous linear map, so it transports
derivatives of plane-valued curves. -/
theorem hasDerivAt_toPlane {q : ℝ → GerverSofa.Point} {q' : GerverSofa.Point} {t : ℝ}
    (hq : HasDerivAt q q' t) : HasDerivAt (fun s => toPlane (q s)) (toPlane q') t := by
  obtain ⟨L, hL⟩ : ∃ L : GerverSofa.Point →L[ℝ] Point, ⇑L = toPlane :=
    ⟨{ toLinearMap := linearEquiv.toLinearMap, cont := continuous_toPlane }, rfl⟩
  rw [← hL]
  simpa [Function.comp_def] using L.hasFDerivAt.comp_hasDerivAt t hq

/-- The coordinate identification `toPlane` preserves smoothness of plane-valued curves. -/
theorem contDiff_toPlane {q : ℝ → GerverSofa.Point} (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ fun t => toPlane (q t) := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · exact hq.fst
  · exact hq.snd

/-! ### Frame readers -/

/-- The angular frame normal is the coordinate image of the standard trigonometric pair. -/
theorem normalVector_coe_eq_toPlane (t : ℝ) :
    normalVector (t : Real.Angle) = toPlane (Real.cos t, Real.sin t) := rfl

/-- The angular frame tangent is the coordinate image of the rotated trigonometric pair. -/
theorem tangentVector_coe_eq_toPlane (t : ℝ) :
    tangentVector (t : Real.Angle) = toPlane (-Real.sin t, Real.cos t) := rfl

/-- The normal component of a body-frame vector rotated by `t` is its first coordinate. -/
theorem inner_toPlane_rot_normalVector (t : ℝ) (z : GerverSofa.Point) :
    inner ℝ (toPlane (rot t z)) (normalVector (t : Real.Angle)) = z.1 := by
  have h := Real.sin_sq_add_cos_sq t
  simp only [normalVector, MovingSofa.frame, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_two, rot, toPlane_zero_coord, toPlane_one_coord, conj_trivial,
    Matrix.cons_val_zero, Matrix.cons_val_one, Real.Angle.cos_coe, Real.Angle.sin_coe]
  linear_combination z.1 * h

/-- The tangential component of a body-frame vector rotated by `t` is its second
coordinate. -/
theorem inner_toPlane_rot_tangentVector (t : ℝ) (z : GerverSofa.Point) :
    inner ℝ (toPlane (rot t z)) (tangentVector (t : Real.Angle)) = z.2 := by
  have h := Real.sin_sq_add_cos_sq t
  simp only [tangentVector, MovingSofa.frame, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_two, rot, toPlane_zero_coord, toPlane_one_coord, conj_trivial,
    Matrix.cons_val_zero, Matrix.cons_val_one, Real.Angle.cos_coe, Real.Angle.sin_coe]
  linear_combination z.2 * h

/-- The normal frame component of a plane point is the vendor scalar product of its
coordinate pair with the vendor normal `u`. -/
theorem inner_normalVector_eq_dot (q : Point) (s : ℝ) :
    inner ℝ q (normalVector (s : Real.Angle)) =
      GerverSofa.dot (fromPlane q) (GerverSofa.u s) := by
  simp only [normalVector, MovingSofa.frame, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Real.Angle.cos_coe,
    Real.Angle.sin_coe, GerverSofa.dot, GerverSofa.u, fromPlane]
  ring

/-- The tangent frame component of a plane point is the vendor scalar product of its
coordinate pair with the vendor tangent `v`. -/
theorem inner_tangentVector_eq_dot (q : Point) (s : ℝ) :
    inner ℝ q (tangentVector (s : Real.Angle)) =
      GerverSofa.dot (fromPlane q) (GerverSofa.v s) := by
  simp only [tangentVector, MovingSofa.frame, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Real.Angle.cos_coe,
    Real.Angle.sin_coe, GerverSofa.dot, GerverSofa.v, fromPlane]
  ring

/-- The angular frame normal is a smooth function of the angle. -/
theorem contDiff_normalVector : ContDiff ℝ ∞ fun t : ℝ => normalVector (t : Real.Angle) := by
  simp only [normalVector_coe_eq_toPlane]
  exact contDiff_toPlane (Real.contDiff_cos.prodMk Real.contDiff_sin)

/-- The angular frame tangent is a smooth function of the angle. -/
theorem contDiff_tangentVector :
    ContDiff ℝ ∞ fun t : ℝ => tangentVector (t : Real.Angle) := by
  simp only [tangentVector_coe_eq_toPlane]
  exact contDiff_toPlane (Real.contDiff_sin.neg.prodMk Real.contDiff_cos)

/-! ### The paper path as a transported direct path

The hypothesis `ContDiff ℝ 1 (path GerverSofa.PartB.params)` in the lemmas below is the
first conjunct of `MovingSofa.gerver_direct_path_regularity`, which lives in a later
module; passing it as a hypothesis keeps this file free of that dependency. -/

/-- The paper path is the coordinate image of the certified direct path. -/
theorem paperGerverPath_eq_toPlane :
    paperGerverPath = fun t => toPlane (path GerverSofa.PartB.params t) := rfl

/-- The paper path differentiates by transporting the derivative of the direct path. -/
theorem hasDerivAt_paperGerverPath (hC1 : ContDiff ℝ 1 (path GerverSofa.PartB.params))
    (t : ℝ) :
    HasDerivAt paperGerverPath (toPlane (deriv (path GerverSofa.PartB.params) t)) t :=
  hasDerivAt_toPlane ((hC1.differentiable one_ne_zero t).hasDerivAt)

/-- The derivative of the paper path is the transported derivative of the direct path. -/
theorem deriv_paperGerverPath (hC1 : ContDiff ℝ 1 (path GerverSofa.PartB.params)) (t : ℝ) :
    deriv paperGerverPath t = toPlane (deriv (path GerverSofa.PartB.params) t) :=
  (hasDerivAt_paperGerverPath hC1 t).deriv

/-- The paper path is continuous. -/
theorem continuous_paperGerverPath (hC1 : ContDiff ℝ 1 (path GerverSofa.PartB.params)) :
    Continuous paperGerverPath := by
  rw [paperGerverPath_eq_toPlane]
  exact continuous_toPlane.comp hC1.continuous

/-- The paper path is continuously differentiable. -/
theorem continuous_deriv_paperGerverPath
    (hC1 : ContDiff ℝ 1 (path GerverSofa.PartB.params)) :
    Continuous (deriv paperGerverPath) := by
  rw [funext (deriv_paperGerverPath hC1)]
  exact continuous_toPlane.comp (hC1.continuous_deriv le_rfl)

end Transport

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Gerver / Paper Set
-/

public section

noncomputable section

namespace MovingSofa

/-- Gerver's paper-frame set, cut out by the explicit path of rotated hallways. -/
@[expose]
def paperGerverSofa : Set Point :=
  (strips (Real.pi / 2)).1 ∩ (strips (Real.pi / 2)).2.2 ∩
    ⋂ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      (fun p ↦ rotationMap (t : Real.Angle) p + paperGerverPath t) '' hallway

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Gerver / Parameters
-/

public section

noncomputable section

namespace MovingSofa

/-- The two Gerver switching angles and the right/left distinguished angles. -/
@[expose]
def paperGerverConstants : (ℝ × ℝ) × (ℝ × ℝ) :=
  ((GerversSofa.φ, GerversSofa.θ), (GerversSofa.φ, Real.pi / 2 - GerversSofa.φ))

/-- The six endpoints of the five Gerver stages. -/
@[expose]
def gerverStageTimes : Fin 6 → ℝ :=
  ![0, GerversSofa.φ, GerversSofa.θ, Real.pi / 2 - GerversSofa.θ,
    Real.pi / 2 - GerversSofa.φ, Real.pi / 2]

/-- The five closed stage intervals in their source order. -/
@[expose]
def gerverStageIntervals (i : Fin 5) : Set ℝ :=
  Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ)

/-- The exact direct 22-equation Gerver system, with the certified phase-map convention. -/
@[expose]
def gerverDirectEquations (p : GerverSofa.Romik.Params) : Prop :=
  GerverSofa.Romik.Equations p

/-- The exact closed rational box for the direct Gerver parameters. -/
@[expose]
def gerverDirectBox : Set GerverSofa.Romik.Params := GerverSofa.Romik.box

/-- The exact box bounds the second-stage linear coefficient `b₁` from below by `-53/100`. -/
theorem gerverDirectBox_b1_lower_bound {p : GerverSofa.Romik.Params} (hp : p ∈ gerverDirectBox) :
    (-53 : ℝ) / 100 ≤ p.b1 := by
  dsimp only [gerverDirectBox, GerverSofa.Romik.box, GerverSofa.qR, Set.mem_ofPred_eq] at hp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, hb1, -⟩ := hp
  exact le_trans (by norm_num) hb1

/-- The exact box bounds the fourth-stage linear coefficient `d₁` from above by `33/25`. -/
theorem gerverDirectBox_d1_upper_bound {p : GerverSofa.Romik.Params} (hp : p ∈ gerverDirectBox) :
    p.d1 ≤ (33 : ℝ) / 25 := by
  dsimp only [gerverDirectBox, GerverSofa.Romik.box, GerverSofa.qR, Set.mem_ofPred_eq] at hp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, -, -, -, -, hd1, -⟩ := hp
  exact le_trans hd1 (by norm_num)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Gerver / Parameter Dictionary
-/

public section

noncomputable section

namespace MovingSofa

/-- Bundle the forward and reverse dictionaries between reduced and full Romik parameters. -/
def gerverParameterDictionary :
    (GerverSofa.Reduced.Params → GerverSofa.Romik.Params) ×
      (GerverSofa.Romik.Params → GerverSofa.Reduced.Params) :=
  (GerverSofa.PartF.Phases.dictionary, GerverSofa.PartF.Phases.undictionary)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Gerver / Partition
-/

public section

noncomputable section

namespace MovingSofa

/-- The ten half-open Gerver phase intervals, indexed from zero. -/
def gerverPhaseIntervals (j : Fin 10) : Set ℝ :=
  let lower (i : Fin 5) := Set.Ico (gerverStageTimes i.castSucc) (gerverStageTimes i.succ)
  Fin.addCases (motive := fun _ ↦ Set ℝ) lower
    (fun i ↦ (fun t ↦ Real.pi - t) '' lower i.rev) j

/-- The ten Gerver phase intervals, written out as explicit half-open real intervals. -/
theorem gerverPhaseIntervals_explicit (j : Fin 10) :
    gerverPhaseIntervals j =
      ![Set.Ico 0 GerversSofa.φ,
        Set.Ico GerversSofa.φ GerversSofa.θ,
        Set.Ico GerversSofa.θ (Real.pi / 2 - GerversSofa.θ),
        Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ),
        Set.Ico (Real.pi / 2 - GerversSofa.φ) (Real.pi / 2),
        Set.Ioc (Real.pi / 2) (Real.pi / 2 + GerversSofa.φ),
        Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi / 2 + GerversSofa.θ),
        Set.Ioc (Real.pi / 2 + GerversSofa.θ) (Real.pi - GerversSofa.θ),
        Set.Ioc (Real.pi - GerversSofa.θ) (Real.pi - GerversSofa.φ),
        Set.Ioc (Real.pi - GerversSofa.φ) Real.pi] j := by
  fin_cases j
  all_goals simp [gerverPhaseIntervals, gerverStageTimes, Fin.addCases, Fin.rev]
  all_goals congr 1 <;> ring

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Gerver / Reverse Physical Domain
-/

public section

noncomputable section

namespace MovingSofa

theorem gerver_reverse_physical_domain (p : GerverSofa.Romik.Params)
    (hp : p ∈ gerverDirectBox) :
    0 < (gerverParameterDictionary.2 p).phi ∧
    (gerverParameterDictionary.2 p).phi < (gerverParameterDictionary.2 p).theta ∧
    (gerverParameterDictionary.2 p).theta < Real.pi / 4 ∧
    0 < (gerverParameterDictionary.2 p).a ∧ 0 < (gerverParameterDictionary.2 p).b ∧
    (39 : ℝ) / 1000 ≤ (gerverParameterDictionary.2 p).phi ∧
    (gerverParameterDictionary.2 p).phi ≤ (40 : ℝ) / 1000 := by
  dsimp [gerverDirectBox, GerverSofa.Romik.box, GerverSofa.qR] at hp
  rcases hp with ⟨_, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _,
    hb1lo, hb1hi, hb2lo, _, _, _, _, _,
    _, _, _, _, _, _, _, _,
    hphilo, hphihi, hthetalo, hthetahi⟩
  norm_num at hb1lo hb1hi hb2lo hphilo hphihi hthetalo hthetahi
  have hphiLo : (39 : ℝ) / 1000 ≤ p.phi := by linarith only [hphilo]
  have hphiHi : p.phi ≤ (1 : ℝ) / 25 := by linarith only [hphihi]
  have hphiPos : (0 : ℝ) < p.phi := by linarith only [hphiLo]
  have hthetaLo : (3 : ℝ) / 5 ≤ p.theta := by linarith only [hthetalo]
  have hthetaHi : p.theta ≤ (7 : ℝ) / 10 := by linarith only [hthetahi]
  have hb1Lo : (-66 : ℝ) / 125 ≤ p.b1 := by linarith only [hb1lo]
  have hb1Hi : p.b1 ≤ (-527 : ℝ) / 1000 := by linarith only [hb1hi]
  have hb2Lo : (23 : ℝ) / 25 ≤ p.b2 := by linarith only [hb2lo]
  have hAPos : (0 : ℝ) < p.phi - 1 - 2 * p.b1 := by linarith only [hphiLo, hb1Hi]
  have hBPos :
      (0 : ℝ) <
        p.b2 + 1 / 2 - (1 + (p.phi - 1 - 2 * p.b1)) * p.phi / 2 + p.phi ^ 2 / 4 := by
    have hprod : (0 : ℝ) ≤ (p.b1 + 66 / 125) * p.phi :=
      mul_nonneg (by linarith only [hb1Lo]) hphiPos.le
    have hsq : (0 : ℝ) ≤ p.phi * (1 / 25 - p.phi) :=
      mul_nonneg hphiPos.le (by linarith only [hphiHi])
    nlinarith only [hb2Lo, hprod, hsq, hphiPos, hphiHi]
  refine ⟨hphiPos, show p.phi < p.theta from ?_,
    show p.theta < Real.pi / 4 from ?_, hAPos, hBPos, hphiLo,
    show p.phi ≤ (40 : ℝ) / 1000 from ?_⟩
  · linarith only [hphiHi, hthetaLo]
  · nlinarith only [hthetaHi, Real.pi_gt_three]
  · linarith only [hphiHi]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Matching and `C¹` regularity of the direct Gerver path

The vendor library assembles the Gerver path `GerverSofa.Romik.path` from five smooth
branches `path1, …, path5` switched at `φ < θ < π/2 - θ < π/2 - φ`.  This file supplies the
differential interface for those branches — each `pathᵢ` has derivative
`rot t (alphaBetaᵢ p t)` — and deduces from the direct equations that values and derivatives
agree at all four switches, hence that `path p` is continuously differentiable with
`path p 0 = 0`.

It also records, for each stage, that the glued path agrees with its analytic branch on the
*closed* stage interval and that `deriv (path p)` is the corresponding `rot t (alphaBetaᵢ p t)`
there, endpoints included.
-/

/-! ### Differential interface for the five direct branches -/

public section

noncomputable section

open scoped ContDiff

namespace GerverSofa.Romik

/-- Rotating a differentiable body-frame curve and translating it differentiates by the
product rule, contributing the infinitesimal rotation `(z₁, z₂) ↦ (-z₂, z₁)`. -/
theorem hasDerivAt_addK_rot {z₁ z₂ : ℝ → ℝ} {z₁' z₂' k₁ k₂ t : ℝ}
    (hz₁ : HasDerivAt z₁ z₁' t) (hz₂ : HasDerivAt z₂ z₂' t) :
    HasDerivAt (fun s => addK (rot s (z₁ s, z₂ s)) k₁ k₂)
      (rot t (z₁' - z₂ t, z₂' + z₁ t)) t := by
  apply HasDerivAt.prodMk
  · change HasDerivAt (fun s => Real.cos s * z₁ s - Real.sin s * z₂ s + k₁)
      (Real.cos t * (z₁' - z₂ t) - Real.sin t * (z₂' + z₁ t)) t
    exact ((((Real.hasDerivAt_cos t).fun_mul hz₁).fun_sub
        ((Real.hasDerivAt_sin t).fun_mul hz₂)).fun_add
      (hasDerivAt_const t k₁)).congr_deriv (by ring)
  · change HasDerivAt (fun s => Real.sin s * z₁ s + Real.cos s * z₂ s + k₂)
      (Real.sin t * (z₁' - z₂ t) + Real.cos t * (z₂' + z₁ t)) t
    exact ((((Real.hasDerivAt_sin t).fun_mul hz₁).fun_add
        ((Real.hasDerivAt_cos t).fun_mul hz₂)).fun_add
      (hasDerivAt_const t k₂)).congr_deriv (by ring)

private theorem hasDerivAt_mul_self (t : ℝ) : HasDerivAt (fun s : ℝ => s * s) (t + t) t := by
  simpa only [id_eq, one_mul, mul_one] using (hasDerivAt_id t).fun_mul (hasDerivAt_id t)

/-- The first direct branch has body-frame velocity `alphaBeta1`. -/
theorem hasDerivAt_path1 (p : Params) (t : ℝ) :
    HasDerivAt (path1 p) (rot t (alphaBeta1 p t)) t := by
  have hz₁ : HasDerivAt (fun s => p.a1 * Real.cos s + p.a2 * Real.sin s - 1)
      (-p.a1 * Real.sin t + p.a2 * Real.cos t) t :=
    ((((Real.hasDerivAt_cos t).const_mul p.a1).fun_add
      ((Real.hasDerivAt_sin t).const_mul p.a2)).fun_sub
      (hasDerivAt_const t (1 : ℝ))).congr_deriv (by ring)
  have hz₂ : HasDerivAt (fun s => -p.a2 * Real.cos s + p.a1 * Real.sin s - 1 / 2)
      (p.a2 * Real.sin t + p.a1 * Real.cos t) t :=
    ((((Real.hasDerivAt_cos t).const_mul (-p.a2)).fun_add
      ((Real.hasDerivAt_sin t).const_mul p.a1)).fun_sub
      (hasDerivAt_const t (1 / 2 : ℝ))).congr_deriv (by ring)
  refine (hasDerivAt_addK_rot (k₁ := p.k11) (k₂ := p.k12) hz₁ hz₂).congr_deriv ?_
  apply congrArg (rot t)
  ext <;> simp [alphaBeta1] <;> ring

/-- The second direct branch has body-frame velocity `alphaBeta2`. -/
theorem hasDerivAt_path2 (p : Params) (t : ℝ) :
    HasDerivAt (path2 p) (rot t (alphaBeta2 p t)) t := by
  have hz₁ : HasDerivAt (fun s => -(1 / 4 : ℝ) * s * s + p.b1 * s + p.b2)
      (-(1 / 2 : ℝ) * t + p.b1) t := by
    have h := (((hasDerivAt_mul_self t).const_mul (-(1 / 4 : ℝ))).fun_add
      ((hasDerivAt_id t).const_mul p.b1)).fun_add (hasDerivAt_const t p.b2)
    simpa only [id_eq, mul_assoc] using h.congr_deriv (by ring)
  have hz₂ : HasDerivAt (fun s => (1 / 2 : ℝ) * s - p.b1 - 1) (1 / 2 : ℝ) t :=
    ((((hasDerivAt_id t).const_mul (1 / 2 : ℝ)).fun_sub (hasDerivAt_const t p.b1)).fun_sub
      (hasDerivAt_const t (1 : ℝ))).congr_deriv (by simp)
  refine (hasDerivAt_addK_rot (k₁ := p.k21) (k₂ := p.k22) hz₁ hz₂).congr_deriv ?_
  apply congrArg (rot t)
  ext <;> simp [alphaBeta2] <;> ring

/-- The third direct branch has body-frame velocity `alphaBeta3`. -/
theorem hasDerivAt_path3 (p : Params) (t : ℝ) :
    HasDerivAt (path3 p) (rot t (alphaBeta3 p t)) t := by
  have hz₁ : HasDerivAt (fun s => p.c1 - s) (-1) t :=
    ((hasDerivAt_const t p.c1).fun_sub (hasDerivAt_id t)).congr_deriv (by simp)
  have hz₂ : HasDerivAt (fun s => p.c2 + s) 1 t :=
    ((hasDerivAt_const t p.c2).fun_add (hasDerivAt_id t)).congr_deriv (by simp)
  refine (hasDerivAt_addK_rot (k₁ := p.k31) (k₂ := p.k32) hz₁ hz₂).congr_deriv ?_
  apply congrArg (rot t)
  ext <;> simp [alphaBeta3] <;> ring

/-- The fourth direct branch has body-frame velocity `alphaBeta4`. -/
theorem hasDerivAt_path4 (p : Params) (t : ℝ) :
    HasDerivAt (path4 p) (rot t (alphaBeta4 p t)) t := by
  have hz₁ : HasDerivAt (fun s => -(1 / 2 : ℝ) * s + p.d1 - 1) (-(1 / 2 : ℝ)) t :=
    ((((hasDerivAt_id t).const_mul (-(1 / 2 : ℝ))).fun_add (hasDerivAt_const t p.d1)).fun_sub
      (hasDerivAt_const t (1 : ℝ))).congr_deriv (by simp)
  have hz₂ : HasDerivAt (fun s => -(1 / 4 : ℝ) * s * s + p.d1 * s + p.d2)
      (-(1 / 2 : ℝ) * t + p.d1) t := by
    have h := (((hasDerivAt_mul_self t).const_mul (-(1 / 4 : ℝ))).fun_add
      ((hasDerivAt_id t).const_mul p.d1)).fun_add (hasDerivAt_const t p.d2)
    simpa only [id_eq, mul_assoc] using h.congr_deriv (by ring)
  refine (hasDerivAt_addK_rot (k₁ := p.k41) (k₂ := p.k42) hz₁ hz₂).congr_deriv ?_
  apply congrArg (rot t)
  ext <;> simp [alphaBeta4] <;> ring

/-- The fifth direct branch has body-frame velocity `alphaBeta5`. -/
theorem hasDerivAt_path5 (p : Params) (t : ℝ) :
    HasDerivAt (path5 p) (rot t (alphaBeta5 p t)) t := by
  have hz₁ : HasDerivAt (fun s => p.e1 * Real.cos s + p.e2 * Real.sin s - 1 / 2)
      (-p.e1 * Real.sin t + p.e2 * Real.cos t) t :=
    ((((Real.hasDerivAt_cos t).const_mul p.e1).fun_add
      ((Real.hasDerivAt_sin t).const_mul p.e2)).fun_sub
      (hasDerivAt_const t (1 / 2 : ℝ))).congr_deriv (by ring)
  have hz₂ : HasDerivAt (fun s => -p.e2 * Real.cos s + p.e1 * Real.sin s - 1)
      (p.e2 * Real.sin t + p.e1 * Real.cos t) t :=
    ((((Real.hasDerivAt_cos t).const_mul (-p.e2)).fun_add
      ((Real.hasDerivAt_sin t).const_mul p.e1)).fun_sub
      (hasDerivAt_const t (1 : ℝ))).congr_deriv (by ring)
  refine (hasDerivAt_addK_rot (k₁ := p.k51) (k₂ := p.k52) hz₁ hz₂).congr_deriv ?_
  apply congrArg (rot t)
  ext <;> simp [alphaBeta5] <;> ring

/-- Continuity of the body-frame velocity field on each branch, transported to the world
frame by the rotation. -/
theorem continuous_rot_alphaBeta1 (p : Params) :
    Continuous fun t : ℝ => rot t (alphaBeta1 p t) := by
  unfold rot alphaBeta1; fun_prop

@[inherit_doc continuous_rot_alphaBeta1]
theorem continuous_rot_alphaBeta2 (p : Params) :
    Continuous fun t : ℝ => rot t (alphaBeta2 p t) := by
  unfold rot alphaBeta2; fun_prop

@[inherit_doc continuous_rot_alphaBeta1]
theorem continuous_rot_alphaBeta3 (p : Params) :
    Continuous fun t : ℝ => rot t (alphaBeta3 p t) := by
  unfold rot alphaBeta3; fun_prop

@[inherit_doc continuous_rot_alphaBeta1]
theorem continuous_rot_alphaBeta4 (p : Params) :
    Continuous fun t : ℝ => rot t (alphaBeta4 p t) := by
  unfold rot alphaBeta4; fun_prop

@[inherit_doc continuous_rot_alphaBeta1]
theorem continuous_rot_alphaBeta5 (p : Params) :
    Continuous fun t : ℝ => rot t (alphaBeta5 p t) := by
  unfold rot alphaBeta5; fun_prop

/-- Equation 32 of the direct system.  The remaining scalar consequences used here are
already extracted by the vendor in `GerverSofa/KernelOnly/EndpointSymmetry.lean`. -/
theorem k11_eq_one_sub_a1_of_equations {p : Params} (heq : Equations p) :
    p.k11 = 1 - p.a1 := by
  have h5 := congrFun heq (5 : Fin 22)
  simp [system] at h5
  linarith

/-! ### Reflection identities for the body-frame velocities

With `S (r, s) = (-s, -r)` the direct equations give `w₃(π/2 - t) = S w₃(t)`,
`w₄(π/2 - t) = S w₂(t)` and `w₅(π/2 - t) = S w₁(t)`. -/

/-- The middle branch velocity is anti-symmetric about `π/4`. -/
theorem alphaBeta3_pi_div_two_sub {p : Params} (heq : Equations p) (t : ℝ) :
    alphaBeta3 p (Real.pi / 2 - t) = (-(alphaBeta3 p t).2, -(alphaBeta3 p t).1) := by
  have hc2 := c2_eq_c1_sub_halfPi_of_equations heq
  simp only [alphaBeta3, Prod.mk.injEq]
  constructor <;> rw [hc2] <;> ring

/-- The fourth branch velocity reflects onto the second. -/
theorem alphaBeta4_pi_div_two_sub {p : Params} (heq : Equations p) (t : ℝ) :
    alphaBeta4 p (Real.pi / 2 - t) = (-(alphaBeta2 p t).2, -(alphaBeta2 p t).1) := by
  have hd1 := d1_eq_quarterPi_sub_b1_of_equations heq
  have hd2 := d2_eq_b2_add_quarterPi_correction_of_equations heq
  simp only [alphaBeta4, alphaBeta2, Prod.mk.injEq]
  constructor <;> simp only [hd1, hd2] <;> ring

/-- The fifth branch velocity reflects onto the first. -/
theorem alphaBeta5_pi_div_two_sub {p : Params} (heq : Equations p) (t : ℝ) :
    alphaBeta5 p (Real.pi / 2 - t) = (-(alphaBeta1 p t).2, -(alphaBeta1 p t).1) := by
  have he1 := e1_eq_a1_of_equations heq
  have he2 := e2_eq_neg_a2_of_equations heq
  simp only [alphaBeta5, alphaBeta1, Prod.mk.injEq, Real.sin_pi_div_two_sub,
    Real.cos_pi_div_two_sub]
  constructor <;> simp only [he1, he2] <;> ring

/-- Velocity matching at the third switch `π/2 - θ`, by reflecting the match at `θ`. -/
theorem alphaBeta34_eq {p : Params} (heq : Equations p) :
    alphaBeta3 p (Real.pi / 2 - p.theta) = alphaBeta4 p (Real.pi / 2 - p.theta) := by
  rw [alphaBeta3_pi_div_two_sub heq, alphaBeta4_pi_div_two_sub heq,
    GerverSofa.PartF.Phases.alphaBeta23_eq heq]

/-- Velocity matching at the fourth switch `π/2 - φ`, by reflecting the match at `φ`. -/
theorem alphaBeta45_eq {p : Params} (heq : Equations p) :
    alphaBeta4 p (Real.pi / 2 - p.phi) = alphaBeta5 p (Real.pi / 2 - p.phi) := by
  rw [alphaBeta4_pi_div_two_sub heq, alphaBeta5_pi_div_two_sub heq,
    GerverSofa.PartF.Phases.alphaBeta12_eq heq]

/-! ### Branch selection on the closed stages

Each stage interval is closed, so the two stages adjacent to a switch both contain it.  The
glued `path` picks the *earlier* branch there, and the certified value-matching equations
say that this is also the later branch's value. -/

/-- The glued direct path unfolds to the nested selection of its five analytic branches. -/
theorem path_eq_ite (p : Params) (t : ℝ) :
    path p t =
      if t ≤ p.phi then path1 p t
      else if t ≤ p.theta then path2 p t
      else if t ≤ Real.pi / 2 - p.theta then path3 p t
      else if t ≤ Real.pi / 2 - p.phi then path4 p t else path5 p t := rfl

/-- On the closed first stage `[0, φ]` the glued path is the first branch. -/
theorem path_eq_path1_of_mem_Icc (p : Params) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) p.phi) :
    path p s = path1 p s := by
  rw [path_eq_ite, ite_eq_left hs.2]

/-- On the closed second stage `[φ, θ]` the glued path is the second branch; at the left
endpoint this is the certified value match `match_path12_of_equations`. -/
theorem path_eq_path2_of_mem_Icc {p : Params} (heq : Equations p) {s : ℝ}
    (hs : s ∈ Set.Icc p.phi p.theta) : path p s = path2 p s := by
  rw [path_eq_ite]
  by_cases hc : s ≤ p.phi
  · obtain rfl : s = p.phi := le_antisymm hc hs.1
    rw [ite_eq_left hc]
    exact match_path12_of_equations heq
  · rw [ite_eq_right hc, ite_eq_left hs.2]

/-- On the closed third stage `[θ, π/2 - θ]` the glued path is the third branch; at the left
endpoint this is the certified value match `match_path23_of_equations`. -/
theorem path_eq_path3_of_mem_Icc {p : Params} (heq : Equations p) (hpt : p.phi < p.theta)
    {s : ℝ} (hs : s ∈ Set.Icc p.theta (Real.pi / 2 - p.theta)) : path p s = path3 p s := by
  have hb := hs.1
  rw [path_eq_ite, ite_eq_right (by linarith : ¬ s ≤ p.phi)]
  by_cases hc : s ≤ p.theta
  · obtain rfl : s = p.theta := le_antisymm hc hs.1
    rw [ite_eq_left hc]
    exact match_path23_of_equations heq
  · rw [ite_eq_right hc, ite_eq_left hs.2]

/-- On the closed fourth stage `[π/2 - θ, π/2 - φ]` the glued path is the fourth branch; at
the left endpoint this is the certified value match `match_path34_of_equations`. -/
theorem path_eq_path4_of_mem_Icc {p : Params} (heq : Equations p) (hpt : p.phi < p.theta)
    (hq : p.theta < Real.pi / 4) {s : ℝ}
    (hs : s ∈ Set.Icc (Real.pi / 2 - p.theta) (Real.pi / 2 - p.phi)) :
    path p s = path4 p s := by
  have hb := hs.1
  rw [path_eq_ite, ite_eq_right (by linarith : ¬ s ≤ p.phi),
    ite_eq_right (by linarith : ¬ s ≤ p.theta)]
  by_cases hc : s ≤ Real.pi / 2 - p.theta
  · obtain rfl : s = Real.pi / 2 - p.theta := le_antisymm hc hs.1
    rw [ite_eq_left hc]
    exact match_path34_of_equations heq
  · rw [ite_eq_right hc, ite_eq_left hs.2]

/-- On the closed fifth stage `[π/2 - φ, π/2]` the glued path is the fifth branch; at the
left endpoint this is the certified value match `match_path45_of_equations`. -/
theorem path_eq_path5_of_mem_Icc {p : Params} (heq : Equations p) (hpt : p.phi < p.theta)
    (hq : p.theta < Real.pi / 4) {s : ℝ}
    (hs : s ∈ Set.Icc (Real.pi / 2 - p.phi) (Real.pi / 2)) : path p s = path5 p s := by
  have hb := hs.1
  rw [path_eq_ite, ite_eq_right (by linarith : ¬ s ≤ p.phi),
    ite_eq_right (by linarith : ¬ s ≤ p.theta),
    ite_eq_right (by linarith : ¬ s ≤ Real.pi / 2 - p.theta)]
  by_cases hc : s ≤ Real.pi / 2 - p.phi
  · obtain rfl : s = Real.pi / 2 - p.phi := le_antisymm hc hs.1
    rw [ite_eq_left hc]
    exact match_path45_of_equations heq
  · rw [ite_eq_right hc]

/-! ### Smoothness of the branches and of their body-frame velocities -/

/-- The first analytic branch is smooth on all of `ℝ`. -/
theorem contDiff_path1 (p : Params) : ContDiff ℝ ∞ (path1 p) := by
  unfold path1 addK rot; fun_prop

@[inherit_doc contDiff_path1]
theorem contDiff_path2 (p : Params) : ContDiff ℝ ∞ (path2 p) := by
  unfold path2 addK rot; fun_prop

@[inherit_doc contDiff_path1]
theorem contDiff_path3 (p : Params) : ContDiff ℝ ∞ (path3 p) := by
  unfold path3 addK rot; fun_prop

@[inherit_doc contDiff_path1]
theorem contDiff_path4 (p : Params) : ContDiff ℝ ∞ (path4 p) := by
  unfold path4 addK rot; fun_prop

@[inherit_doc contDiff_path1]
theorem contDiff_path5 (p : Params) : ContDiff ℝ ∞ (path5 p) := by
  unfold path5 addK rot; fun_prop

/-- The first body-frame velocity pair is smooth on all of `ℝ`. -/
theorem contDiff_alphaBeta1 (p : Params) : ContDiff ℝ ∞ (alphaBeta1 p) := by
  unfold alphaBeta1; fun_prop

@[inherit_doc contDiff_alphaBeta1]
theorem contDiff_alphaBeta2 (p : Params) : ContDiff ℝ ∞ (alphaBeta2 p) := by
  unfold alphaBeta2; fun_prop

@[inherit_doc contDiff_alphaBeta1]
theorem contDiff_alphaBeta3 (p : Params) : ContDiff ℝ ∞ (alphaBeta3 p) := by
  unfold alphaBeta3; fun_prop

@[inherit_doc contDiff_alphaBeta1]
theorem contDiff_alphaBeta4 (p : Params) : ContDiff ℝ ∞ (alphaBeta4 p) := by
  unfold alphaBeta4; fun_prop

@[inherit_doc contDiff_alphaBeta1]
theorem contDiff_alphaBeta5 (p : Params) : ContDiff ℝ ∞ (alphaBeta5 p) := by
  unfold alphaBeta5; fun_prop

/-! ### The stage derivatives, endpoints included

A nondegenerate closed interval has a unique tangent direction at each of its points,
including its endpoints, so a `C¹` function agreeing there with a differentiable curve
already has that curve's derivative at every point of the interval. -/

/-- If the `C¹` glued path agrees on a nondegenerate closed interval with a curve whose
derivative is `rot s (W s)`, then that is its derivative everywhere on the interval,
endpoints included. -/
theorem deriv_path_of_eqOn_Icc {p : Params} (hC1 : ContDiff ℝ 1 (path p))
    {X W : ℝ → Point} {a b t : ℝ} (hab : a < b)
    (hX : ∀ s, HasDerivAt X (rot s (W s)) s) (hXe : ∀ s ∈ Set.Icc a b, path p s = X s)
    (ht : t ∈ Set.Icc a b) : deriv (path p) t = rot t (W t) := by
  have h1 : HasDerivWithinAt (path p) (deriv (path p) t) (Set.Icc a b) t :=
    ((hC1.differentiable one_ne_zero t).hasDerivAt).hasDerivWithinAt
  have h2 : HasDerivWithinAt (path p) (rot t (W t)) (Set.Icc a b) t :=
    ((hX t).hasDerivWithinAt).congr hXe (hXe t ht)
  exact (uniqueDiffOn_Icc hab t ht).eq_deriv _ h1 h2

/-- On the closed first stage the glued path has body-frame velocity `alphaBeta1`. -/
theorem deriv_path_eq_rot_alphaBeta1 {p : Params} (hC1 : ContDiff ℝ 1 (path p))
    (hphi : 0 < p.phi) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) p.phi) :
    deriv (path p) t = rot t (alphaBeta1 p t) :=
  deriv_path_of_eqOn_Icc hC1 hphi (hasDerivAt_path1 p)
    (fun _ hs => path_eq_path1_of_mem_Icc p hs) ht

/-- On the closed second stage the glued path has body-frame velocity `alphaBeta2`. -/
theorem deriv_path_eq_rot_alphaBeta2 {p : Params} (hC1 : ContDiff ℝ 1 (path p))
    (heq : Equations p) (hpt : p.phi < p.theta) {t : ℝ} (ht : t ∈ Set.Icc p.phi p.theta) :
    deriv (path p) t = rot t (alphaBeta2 p t) :=
  deriv_path_of_eqOn_Icc hC1 hpt (hasDerivAt_path2 p)
    (fun _ hs => path_eq_path2_of_mem_Icc heq hs) ht

/-- On the closed third stage the glued path has body-frame velocity `alphaBeta3`. -/
theorem deriv_path_eq_rot_alphaBeta3 {p : Params} (hC1 : ContDiff ℝ 1 (path p))
    (heq : Equations p) (hpt : p.phi < p.theta) (hq : p.theta < Real.pi / 4) {t : ℝ}
    (ht : t ∈ Set.Icc p.theta (Real.pi / 2 - p.theta)) :
    deriv (path p) t = rot t (alphaBeta3 p t) :=
  deriv_path_of_eqOn_Icc hC1 (by linarith) (hasDerivAt_path3 p)
    (fun _ hs => path_eq_path3_of_mem_Icc heq hpt hs) ht

/-- On the closed fourth stage the glued path has body-frame velocity `alphaBeta4`. -/
theorem deriv_path_eq_rot_alphaBeta4 {p : Params} (hC1 : ContDiff ℝ 1 (path p))
    (heq : Equations p) (hpt : p.phi < p.theta) (hq : p.theta < Real.pi / 4) {t : ℝ}
    (ht : t ∈ Set.Icc (Real.pi / 2 - p.theta) (Real.pi / 2 - p.phi)) :
    deriv (path p) t = rot t (alphaBeta4 p t) :=
  deriv_path_of_eqOn_Icc hC1 (by linarith) (hasDerivAt_path4 p)
    (fun _ hs => path_eq_path4_of_mem_Icc heq hpt hq hs) ht

/-- On the closed fifth stage the glued path has body-frame velocity `alphaBeta5`. -/
theorem deriv_path_eq_rot_alphaBeta5 {p : Params} (hC1 : ContDiff ℝ 1 (path p))
    (heq : Equations p) (hphi : 0 < p.phi) (hpt : p.phi < p.theta)
    (hq : p.theta < Real.pi / 4) {t : ℝ}
    (ht : t ∈ Set.Icc (Real.pi / 2 - p.phi) (Real.pi / 2)) :
    deriv (path p) t = rot t (alphaBeta5 p t) :=
  deriv_path_of_eqOn_Icc hC1 (by linarith) (hasDerivAt_path5 p)
    (fun _ hs => path_eq_path5_of_mem_Icc heq hpt hq hs) ht

end GerverSofa.Romik

namespace MovingSofa

open GerverSofa.Romik

/-- The five explicit Romik path branches for a parameter tuple. -/
def gerverDirectBranches (p : GerverSofa.Romik.Params) : Fin 5 → ℝ → GerverSofa.Point :=
  ![GerverSofa.Romik.path1 p, GerverSofa.Romik.path2 p, GerverSofa.Romik.path3 p,
    GerverSofa.Romik.path4 p, GerverSofa.Romik.path5 p]

/-- The four switching times separating the explicit Romik path branches. -/
def gerverDirectSwitches (p : GerverSofa.Romik.Params) : Fin 4 → ℝ :=
  ![p.phi, p.theta, Real.pi / 2 - p.theta, Real.pi / 2 - p.phi]

theorem gerver_direct_path_regularity (p : GerverSofa.Romik.Params)
    (hp : p ∈ gerverDirectBox) (heq : gerverDirectEquations p) :
    ContDiff ℝ 1 (GerverSofa.Romik.path p) ∧ GerverSofa.Romik.path p 0 = 0 ∧
    ∀ i : Fin 4,
      gerverDirectBranches p i.castSucc (gerverDirectSwitches p i) =
        gerverDirectBranches p i.succ (gerverDirectSwitches p i) ∧
      deriv (gerverDirectBranches p i.castSucc) (gerverDirectSwitches p i) =
        deriv (gerverDirectBranches p i.succ) (gerverDirectSwitches p i) := by
  -- The switching angles are strictly ordered by the reverse-domain bounds.
  have hdom := gerver_reverse_physical_domain p hp
  have hphi_pos : 0 < p.phi := hdom.1
  have hphi_theta : p.phi < p.theta := hdom.2.1
  have htheta_quarter : p.theta < Real.pi / 4 := hdom.2.2.1
  have htheta_eta : p.theta < Real.pi / 2 - p.theta := by linarith
  have heta_tau : Real.pi / 2 - p.theta < Real.pi / 2 - p.phi := by linarith
  -- The body-frame velocity matches at the four switches.
  have hw12 := GerverSofa.PartF.Phases.alphaBeta12_eq (p := p) heq
  have hw23 := GerverSofa.PartF.Phases.alphaBeta23_eq (p := p) heq
  have hw34 := alphaBeta34_eq (p := p) heq
  have hw45 := alphaBeta45_eq (p := p) heq
  -- The four positional matches, from the certified vendor extraction.
  have hv12 := match_path12_of_equations (p := p) heq
  have hv23 := match_path23_of_equations (p := p) heq
  have hv34 := match_path34_of_equations (p := p) heq
  have hv45 := match_path45_of_equations (p := p) heq
  -- Glue the branches from the last switch backwards.
  have hD45 : ∀ t : ℝ, HasDerivAt
      (fun s => if s ≤ Real.pi / 2 - p.phi then path4 p s else path5 p s)
      (if t ≤ Real.pi / 2 - p.phi then rot t (alphaBeta4 p t)
        else rot t (alphaBeta5 p t)) t :=
    hasDerivAt_if_le (hasDerivAt_path4 p) (hasDerivAt_path5 p) hv45
      (congrArg (rot (Real.pi / 2 - p.phi)) hw45)
  have hC45 : Continuous fun t : ℝ =>
      if t ≤ Real.pi / 2 - p.phi then rot t (alphaBeta4 p t) else rot t (alphaBeta5 p t) :=
    (continuous_rot_alphaBeta4 p).if_le (continuous_rot_alphaBeta5 p)
      continuous_id continuous_const (by
        intro t ht
        subst ht
        exact congrArg (rot (Real.pi / 2 - p.phi)) hw45)
  have hD345 : ∀ t : ℝ, HasDerivAt
      (fun s => if s ≤ Real.pi / 2 - p.theta then path3 p s
        else if s ≤ Real.pi / 2 - p.phi then path4 p s else path5 p s)
      (if t ≤ Real.pi / 2 - p.theta then rot t (alphaBeta3 p t)
        else if t ≤ Real.pi / 2 - p.phi then rot t (alphaBeta4 p t)
        else rot t (alphaBeta5 p t)) t :=
    hasDerivAt_if_le (hasDerivAt_path3 p) hD45
      (by rw [ite_eq_left heta_tau.le]; exact hv34)
      (by rw [ite_eq_left heta_tau.le]
          exact congrArg (rot (Real.pi / 2 - p.theta)) hw34)
  have hC345 : Continuous fun t : ℝ =>
      if t ≤ Real.pi / 2 - p.theta then rot t (alphaBeta3 p t)
      else if t ≤ Real.pi / 2 - p.phi then rot t (alphaBeta4 p t)
      else rot t (alphaBeta5 p t) :=
    (continuous_rot_alphaBeta3 p).if_le hC45 continuous_id continuous_const (by
      intro t ht
      subst ht
      rw [ite_eq_left heta_tau.le]
      exact congrArg (rot (Real.pi / 2 - p.theta)) hw34)
  have hD2345 : ∀ t : ℝ, HasDerivAt
      (fun s => if s ≤ p.theta then path2 p s
        else if s ≤ Real.pi / 2 - p.theta then path3 p s
        else if s ≤ Real.pi / 2 - p.phi then path4 p s else path5 p s)
      (if t ≤ p.theta then rot t (alphaBeta2 p t)
        else if t ≤ Real.pi / 2 - p.theta then rot t (alphaBeta3 p t)
        else if t ≤ Real.pi / 2 - p.phi then rot t (alphaBeta4 p t)
        else rot t (alphaBeta5 p t)) t :=
    hasDerivAt_if_le (hasDerivAt_path2 p) hD345
      (by rw [ite_eq_left htheta_eta.le]; exact hv23)
      (by rw [ite_eq_left htheta_eta.le]
          exact congrArg (rot p.theta) hw23)
  have hC2345 : Continuous fun t : ℝ =>
      if t ≤ p.theta then rot t (alphaBeta2 p t)
      else if t ≤ Real.pi / 2 - p.theta then rot t (alphaBeta3 p t)
      else if t ≤ Real.pi / 2 - p.phi then rot t (alphaBeta4 p t)
      else rot t (alphaBeta5 p t) :=
    (continuous_rot_alphaBeta2 p).if_le hC345 continuous_id continuous_const (by
      intro t ht
      subst ht
      rw [ite_eq_left htheta_eta.le]
      exact congrArg (rot p.theta) hw23)
  have hDpath : ∀ t : ℝ, HasDerivAt (path p)
      (if t ≤ p.phi then rot t (alphaBeta1 p t)
        else if t ≤ p.theta then rot t (alphaBeta2 p t)
        else if t ≤ Real.pi / 2 - p.theta then rot t (alphaBeta3 p t)
        else if t ≤ Real.pi / 2 - p.phi then rot t (alphaBeta4 p t)
        else rot t (alphaBeta5 p t)) t :=
    hasDerivAt_if_le (hasDerivAt_path1 p) hD2345
      (by rw [ite_eq_left hphi_theta.le]; exact hv12)
      (by rw [ite_eq_left hphi_theta.le]
          exact congrArg (rot p.phi) hw12)
  have hCpath : Continuous fun t : ℝ =>
      if t ≤ p.phi then rot t (alphaBeta1 p t)
      else if t ≤ p.theta then rot t (alphaBeta2 p t)
      else if t ≤ Real.pi / 2 - p.theta then rot t (alphaBeta3 p t)
      else if t ≤ Real.pi / 2 - p.phi then rot t (alphaBeta4 p t)
      else rot t (alphaBeta5 p t) :=
    (continuous_rot_alphaBeta1 p).if_le hC2345 continuous_id continuous_const (by
      intro t ht
      subst ht
      rw [ite_eq_left hphi_theta.le]
      exact congrArg (rot p.phi) hw12)
  -- The four derivative matches.
  have hdv12 : deriv (path1 p) p.phi = deriv (path2 p) p.phi := by
    rw [(hasDerivAt_path1 p p.phi).deriv, (hasDerivAt_path2 p p.phi).deriv, hw12]
  have hdv23 : deriv (path2 p) p.theta = deriv (path3 p) p.theta := by
    rw [(hasDerivAt_path2 p p.theta).deriv, (hasDerivAt_path3 p p.theta).deriv, hw23]
  have hdv34 : deriv (path3 p) (Real.pi / 2 - p.theta) =
      deriv (path4 p) (Real.pi / 2 - p.theta) := by
    rw [(hasDerivAt_path3 p _).deriv, (hasDerivAt_path4 p _).deriv, hw34]
  have hdv45 : deriv (path4 p) (Real.pi / 2 - p.phi) =
      deriv (path5 p) (Real.pi / 2 - p.phi) := by
    rw [(hasDerivAt_path4 p _).deriv, (hasDerivAt_path5 p _).deriv, hw45]
  refine ⟨contDiff_one_of_hasDerivAt hDpath hCpath, ?_, ?_⟩
  · -- `0 < φ` selects the first branch, and the normalizations make it vanish at `0`.
    have hk11 := k11_eq_one_sub_a1_of_equations (p := p) heq
    have hk12 := k12_eq_quarter_of_equations (p := p) heq
    have ha2 := a2_eq_neg_quarter_of_equations (p := p) heq
    have h0 : path p 0 = path1 p 0 := by
      unfold GerverSofa.Romik.path
      exact ite_eq_left hphi_pos.le
    rw [h0]
    simp only [path1, addK, rot, Real.cos_zero, Real.sin_zero, Prod.ext_iff, Prod.fst_zero,
      Prod.snd_zero]
    constructor <;> linarith
  · intro i
    fin_cases i
    · exact ⟨hv12, hdv12⟩
    · exact ⟨hv23, hdv23⟩
    · exact ⟨hv34, hdv34⟩
    · exact ⟨hv45, hdv45⟩

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Gerver / Literal Sets
-/

public section

noncomputable section

namespace MovingSofa

/-- The outer cap defined by all upper path support constraints and the horizontal base. -/
@[expose]
def gerverOuterCap : Set Point :=
  {q | 0 ≤ q 1 ∧ ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
    inner ℝ q (normalVector (t : Real.Angle)) ≤
      inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 ∧
    inner ℝ q (tangentVector (t : Real.Angle)) ≤
      inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1}

/-- The union of strict forbidden inner corners above the horizontal base along the Gerver
path. -/
@[expose]
def gerverLiteralNiche : Set Point :=
  {q | 0 ≤ q 1 ∧ ∃ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
    inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)) < 0 ∧
    inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle)) < 0}

/-- The literal Gerver sofa obtained by removing its niche from its outer cap. -/
@[expose]
def gerverLiteralSofa : Set Point := gerverOuterCap \ gerverLiteralNiche

/-- Bundle the literal niche and sofa sets for comparison with the canonical definitions. -/
def gerverLiteralSets : Set Point × Set Point := (gerverLiteralNiche, gerverLiteralSofa)

/-- The paper outer cap is the coordinate transport of the certified Romik cap `K₀`. -/
theorem mem_gerverOuterCap_iff (q : Point) :
    q ∈ gerverOuterCap ↔
      GerverSofa.PartF.Coordinates.fromPlane q ∈
        GerverSofa.Romik.K0 GerverSofa.PartB.params := by
  simp only [gerverOuterCap, Set.mem_ofPred_eq, GerverSofa.Romik.mem_K0, Set.mem_inter_iff,
    GerverSofa.Romik.mem_supportHalfU, GerverSofa.Romik.mem_supportHalfV,
    inner_normalVector_eq_dot, inner_tangentVector_eq_dot]
  exact Iff.rfl

/-- A point whose coordinate pair lies in the certified Romik cap `K₀` lies in the paper
outer cap. -/
theorem toPlane_mem_gerverOuterCap {x : GerverSofa.Point}
    (hx : x ∈ GerverSofa.Romik.K0 GerverSofa.PartB.params) :
    GerverSofa.PartF.Coordinates.toPlane x ∈ gerverOuterCap :=
  (mem_gerverOuterCap_iff _).2 (by rwa [GerverSofa.PartF.Coordinates.fromPlane_toPlane])

/-- The paper literal niche is the coordinate transport of the certified Romik niche. -/
theorem mem_gerverLiteralNiche_iff (q : Point) :
    q ∈ gerverLiteralNiche ↔
      GerverSofa.PartF.Coordinates.fromPlane q ∈
        GerverSofa.Romik.niche GerverSofa.PartB.params := by
  have hsub : ∀ (r : Point) (t : ℝ),
      GerverSofa.PartF.Coordinates.fromPlane (r - paperGerverPath t) =
        ((GerverSofa.PartF.Coordinates.fromPlane r).1 -
            (GerverSofa.Romik.path GerverSofa.PartB.params t).1,
          (GerverSofa.PartF.Coordinates.fromPlane r).2 -
            (GerverSofa.Romik.path GerverSofa.PartB.params t).2) := fun _ _ => rfl
  constructor
  · rintro ⟨hy, t, ht, h1, h2⟩
    rw [inner_normalVector_eq_dot, hsub] at h1
    rw [inner_tangentVector_eq_dot, hsub] at h2
    exact ⟨hy, t, ht, h1, h2⟩
  · rintro ⟨hy, t, ht, h1, h2⟩
    refine ⟨hy, t, ht, ?_, ?_⟩
    · rw [inner_normalVector_eq_dot, hsub]; exact h1
    · rw [inner_tangentVector_eq_dot, hsub]; exact h2

theorem paperGerverSofa_eq_literal : paperGerverSofa = gerverLiteralSofa := by
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  have hmemhall : ∀ (t : Real.Angle) (v q : Point),
      q ∈ (fun p ↦ rotationMap t p + v) '' hallway ↔
        (inner ℝ (q - v) (normalVector t) ≤ 1 ∧
          inner ℝ (q - v) (tangentVector t) ≤ 1) ∧
        (0 ≤ inner ℝ (q - v) (normalVector t) ∨
          0 ≤ inner ℝ (q - v) (tangentVector t)) := by
    intro t v q
    constructor
    · rintro ⟨p, hp, rfl⟩
      have h0 : inner ℝ (rotationMap t p + v - v) (normalVector t) = p 0 := by
        rw [add_sub_cancel_right, inner_rotationMap_normalVector]
      have h1 : inner ℝ (rotationMap t p + v - v) (tangentVector t) = p 1 := by
        rw [add_sub_cancel_right, inner_rotationMap_tangentVector]
      simp only [h0, h1]
      exact (mem_hallway_iff p).1 hp
    · intro h
      obtain ⟨p, hp⟩ := (EuclideanGeometry.o.rotation t).surjective (q - v)
      have hpq : rotationMap t p = q - v := hp
      have h0 : p 0 = inner ℝ (q - v) (normalVector t) := by
        rw [← inner_rotationMap_normalVector p t, hpq]
      have h1 : p 1 = inner ℝ (q - v) (tangentVector t) := by
        rw [← inner_rotationMap_tangentVector p t, hpq]
      refine ⟨p, (mem_hallway_iff p).2 ?_, ?_⟩
      · rw [h0, h1]; exact h
      · change rotationMap t p + v = q
        rw [hpq]; abel
  have hconttan : Continuous (fun t : ℝ ↦ tangentVector (t : Real.Angle)) := by
    let c : ℝ → (i : Fin 2) → ℝ :=
      fun t i ↦ Fin.cases (-Real.sin t) (fun _ ↦ Real.cos t) i
    have hc : Continuous c := by
      apply continuous_pi
      intro i
      fin_cases i
      · exact Real.continuous_sin.neg
      · exact Real.continuous_cos
    have heq : (fun t : ℝ ↦ tangentVector (t : Real.Angle)) =
        (fun t ↦ WithLp.toLp 2 (c t)) := by
      funext t
      ext i
      fin_cases i <;> rfl
    rw [heq]
    exact (PiLp.continuous_toLp (2 : ENNReal) (fun _ : Fin 2 ↦ ℝ)).comp hc
  have hreg := gerver_direct_path_regularity GerverSofa.PartB.params
    GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  have hpathcont : Continuous paperGerverPath :=
    GerverSofa.PartF.Coordinates.continuous_toPlane.comp hreg.1.continuous
  have hpath0 : paperGerverPath 0 = 0 := by
    change GerverSofa.PartF.Coordinates.toPlane
      (GerverSofa.Romik.path GerverSofa.PartB.params 0) = 0
    rw [hreg.2.1]
    ext i
    fin_cases i <;> rfl
  have hstrip : ∀ q : Point,
      q ∈ (strips (Real.pi / 2)).1 ∩ (strips (Real.pi / 2)).2.2 ↔ 0 ≤ q 1 ∧ q 1 ≤ 1 := by
    intro q
    have h := mem_stripParallelogram_iff (Real.pi / 2) q
    rw [inner_normalVector_pi_div_two] at h
    have hset : (strips (Real.pi / 2)).1 ∩ (strips (Real.pi / 2)).2.2 =
        (stripParallelogram (Real.pi / 2)).1 := rfl
    rw [hset, h]
    tauto
  have hshift : ∀ w z n : Point,
      (inner ℝ w n ≤ inner ℝ z n + 1 ↔ inner ℝ (w - z) n ≤ 1) := by
    intro w z n
    rw [inner_sub_left]
    constructor <;> intro h <;> linarith
  ext q
  constructor
  · rintro ⟨hs, hint⟩
    have hhall : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        (inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)) ≤ 1 ∧
          inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle)) ≤ 1) ∧
        (0 ≤ inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)) ∨
          0 ≤ inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle))) := fun t ht ↦
      (hmemhall _ _ _).1 (Set.mem_iInter₂.1 hint t ht)
    refine ⟨⟨((hstrip q).1 hs).1, fun t ht ↦
      ⟨(hshift _ _ _).2 (hhall t ht).1.1, (hshift _ _ _).2 (hhall t ht).1.2⟩⟩, ?_⟩
    rintro ⟨-, t, ht, hlt1, hlt2⟩
    rcases (hhall t (Set.Ioo_subset_Icc_self ht)).2 with h | h
    · linarith
    · linarith
  · rintro ⟨⟨hy, hcap⟩, hniche⟩
    have hcap' : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)) ≤ 1 ∧
        inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle)) ≤ 1 := fun t ht ↦
      ⟨(hshift _ _ _).1 (hcap t ht).1, (hshift _ _ _).1 (hcap t ht).2⟩
    have hopen : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        0 ≤ inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)) ∨
        0 ≤ inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle)) := by
      intro t ht
      by_contra hcon
      exact hniche ⟨hy, t, ht, not_le.mp fun h ↦ hcon (Or.inl h),
        not_le.mp fun h ↦ hcon (Or.inr h)⟩
    have hclosed : IsClosed {t : ℝ |
        0 ≤ max (inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)))
          (inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle)))} :=
      isClosed_le continuous_const
        (((continuous_const.sub hpathcont).inner continuous_normalVector_real).max
          ((continuous_const.sub hpathcont).inner hconttan))
    have hIcc : Set.Icc (0 : ℝ) (Real.pi / 2) ⊆ {t : ℝ |
        0 ≤ max (inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)))
          (inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle)))} := by
      rw [← closure_Ioo (ne_of_lt hTpos)]
      exact hclosed.closure_subset_iff.mpr fun t ht ↦ le_max_iff.mpr (hopen t ht)
    have hy1 : q 1 ≤ 1 := by
      have h := (hcap' 0 (Set.left_mem_Icc.mpr hTpos.le)).2
      rwa [hpath0, sub_zero, inner_tangentVector_zero] at h
    refine ⟨(hstrip q).2 ⟨hy, hy1⟩, Set.mem_iInter₂.2 fun t ht ↦ ?_⟩
    exact (hmemhall _ _ _).2
      ⟨hcap' t ht, le_max_iff.mp (hIcc ht)⟩

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Gerver / Literal Connected
-/

public section

noncomputable section

namespace MovingSofa

theorem gerver_literal_connected : IsConnected gerverLiteralSofa := by
  have hu : ∀ (q : Point) (t : ℝ),
      inner ℝ q (normalVector (t : Real.Angle)) =
        GerverSofa.dot (GerverSofa.PartF.Coordinates.fromPlane q) (GerverSofa.u t) := by
    intro q t
    simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two, GerverSofa.dot,
      GerverSofa.u, GerverSofa.PartF.Coordinates.fromPlane, mul_comm]
  have hv : ∀ (q : Point) (t : ℝ),
      inner ℝ q (tangentVector (t : Real.Angle)) =
        GerverSofa.dot (GerverSofa.PartF.Coordinates.fromPlane q) (GerverSofa.v t) := by
    intro q t
    simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two, GerverSofa.dot,
      GerverSofa.v, GerverSofa.PartF.Coordinates.fromPlane, mul_comm]
  have hpath : ∀ t : ℝ,
      GerverSofa.PartF.Coordinates.fromPlane (paperGerverPath t) =
        GerverSofa.Romik.path GerverSofa.PartC.params t := fun _ => rfl
  have hcap : ∀ q : Point,
      q ∈ gerverOuterCap ↔
        GerverSofa.PartF.Coordinates.fromPlane q ∈
          GerverSofa.Romik.K0 GerverSofa.PartC.params := by
    intro q
    constructor
    · rintro ⟨hy, hs⟩
      refine ⟨hy, fun t ht => ?_⟩
      obtain ⟨h1, h2⟩ := hs t ht
      rw [hu, hu, hpath] at h1
      rw [hv, hv, hpath] at h2
      exact ⟨h1, h2⟩
    · rintro ⟨hy, hs⟩
      refine ⟨hy, fun t ht => ?_⟩
      obtain ⟨h1, h2⟩ := hs t ht
      rw [hu, hu, hpath]
      rw [hv, hv, hpath]
      exact ⟨h1, h2⟩
  have hsub : ∀ (q : Point) (t : ℝ),
      GerverSofa.PartF.Coordinates.fromPlane (q - paperGerverPath t) =
        ((GerverSofa.PartF.Coordinates.fromPlane q).1 -
            (GerverSofa.Romik.path GerverSofa.PartC.params t).1,
          (GerverSofa.PartF.Coordinates.fromPlane q).2 -
            (GerverSofa.Romik.path GerverSofa.PartC.params t).2) := fun _ _ => rfl
  have hniche : ∀ q : Point,
      q ∈ gerverLiteralNiche ↔
        GerverSofa.PartF.Coordinates.fromPlane q ∈
          GerverSofa.Romik.niche GerverSofa.PartC.params := by
    intro q
    constructor
    · rintro ⟨hy, t, ht, h1, h2⟩
      rw [hu, hsub] at h1
      rw [hv, hsub] at h2
      exact ⟨hy, t, ht, h1, h2⟩
    · rintro ⟨hy, t, ht, h1, h2⟩
      refine ⟨hy, t, ht, ?_, ?_⟩
      · rw [hu, hsub]; exact h1
      · rw [hv, hsub]; exact h2
  have hset : gerverLiteralSofa =
      GerverSofa.PartF.Coordinates.toPlane '' GerverSofa.PartC.G := by
    rw [GerverSofa.PartF.Coordinates.image_eq_preimage]
    ext q
    exact and_congr (hcap q) (not_congr (hniche q))
  rw [hset]
  exact GerverSofa.PartF.Coordinates.isConnected_image
    GerverSofa.PartC.Stage4.G_connected_direct

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Gerver / Parameter Identification
-/

public section

noncomputable section

namespace MovingSofa

open GerverSofa.PartF.ProjectAdapter (selected)

/-- The adapter's selected reverse parameter vector carries the paper's angle `φ` in its
`phi` field.  This is true by definition — `selected` is built from the very quadruple that
defines `GerversSofa.φ` — but it is the only bridge from the vendor parameter vector to the
paper's stage times `gerverStageTimes`, so it is recorded as a named lemma rather than left
to an invisible unfolding at each use site. -/
theorem selected_phi : selected.phi = GerversSofa.φ := rfl

/-- The adapter's selected reverse parameter vector carries the paper's angle `θ` in its
`theta` field; see `selected_phi` for why this `rfl` is worth naming. -/
theorem selected_theta : selected.theta = GerversSofa.θ := rfl

theorem gerver_parameter_identification :
    (∀ p : GerverSofa.Romik.Params, p ∈ gerverDirectBox → gerverDirectEquations p →
      p = gerverParameterDictionary.1 selected ∧
      p.phi = selected.phi ∧ p.theta = selected.theta ∧
      0 < selected.phi ∧ selected.phi < selected.theta ∧ selected.theta < Real.pi / 4 ∧
      (39 : ℝ) / 1000 ≤ selected.phi ∧ selected.phi ≤ (40 : ℝ) / 1000 ∧
      GerversSofa.ABφθSpec selected.a selected.b selected.phi selected.theta) ∧
    (∃ p : GerverSofa.Romik.Params, p ∈ gerverDirectBox ∧ gerverDirectEquations p ∧
      p = gerverParameterDictionary.1 selected) := by
  -- The reverse parameters of any direct solution in the box satisfy the whole
  -- reduced specification, whose unique solution is the selected quadruple.
  have key : ∀ p : GerverSofa.Romik.Params, p ∈ gerverDirectBox → gerverDirectEquations p →
      gerverParameterDictionary.2 p = selected := by
    intro p hp heq
    rw [GerverSofa.PartF.ProjectAdapter.selected_eq_certified]
    exact GerverSofa.PartF.Parameters.undictionary_eq_reduced_certified hp heq
  -- Reconstruction then recovers the direct vector from its reverse parameters.
  have hdict : ∀ p : GerverSofa.Romik.Params, p ∈ gerverDirectBox → gerverDirectEquations p →
      p = gerverParameterDictionary.1 selected := by
    intro p hp heq
    calc p = GerverSofa.PartF.Phases.dictionary (gerverParameterDictionary.2 p) :=
          (GerverSofa.PartF.Phases.dictionary_undictionary_of_equations heq).symm
      _ = gerverParameterDictionary.1 selected :=
          congrArg GerverSofa.PartF.Phases.dictionary (key p hp heq)
  have hspec : GerversSofa.ABφθSpec selected.a selected.b selected.phi selected.theta :=
    GerversSofa.ABφθSpec.existsUnique.choose_spec.1
  refine ⟨fun p hp heq => ?_, GerverSofa.PartB.params, GerverSofa.PartB.params_mem,
    GerverSofa.PartB.params_equations,
    hdict _ GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations⟩
  obtain ⟨hphipos, hphitheta, htheta, -, -, hphilo, hphihi⟩ :=
    gerver_reverse_physical_domain p hp
  have hu := key p hp heq
  rw [hu] at hphipos hphitheta htheta hphilo hphihi
  exact ⟨hdict p hp heq, congrArg GerverSofa.Reduced.Params.phi hu,
    congrArg GerverSofa.Reduced.Params.theta hu, hphipos, hphitheta, htheta, hphilo, hphihi,
    hspec⟩

/-- The two distinguished Gerver angles are interior and complementary. -/
theorem paperGerverConstants_snd_mem_Ioo :
    paperGerverConstants.2.1 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) ∧
      paperGerverConstants.2.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) ∧
      paperGerverConstants.2.1 + paperGerverConstants.2.2 = Real.pi / 2 := by
  have hpos : 0 < GerversSofa.φ := by
    obtain ⟨hall, q, hqbox, hqeq, -⟩ := gerver_parameter_identification
    exact (hall q hqbox hqeq).2.2.2.1
  have hle : GerversSofa.φ ≤ Real.pi / 4 := by
    have h := GerversSofa.ABφθSpec.existsUnique.choose_spec.1
    exact le_trans h.2.1 h.2.2.1
  have hpi := Real.pi_pos
  have h1 : paperGerverConstants.2.1 = GerversSofa.φ := rfl
  have h2 : paperGerverConstants.2.2 = Real.pi / 2 - GerversSofa.φ := rfl
  rw [h1, h2]
  refine ⟨⟨hpos, by linarith only [hle, hpi]⟩,
    ⟨by linarith only [hle, hpi], by linarith only [hpos]⟩, by ring⟩

/-- The two distinguished angles are ordered: the certified bound `φ ≤ 1/25` puts `φ` well below
`π/4 = π/2 - π/4`. -/
theorem paperGerverConstants_snd_fst_lt_snd_snd :
    paperGerverConstants.2.1 < paperGerverConstants.2.2 := by
  obtain ⟨-, -, hsum⟩ := paperGerverConstants_snd_mem_Ioo
  have hphi : paperGerverConstants.2.1 ≤ (40 : ℝ) / 1000 := by
    obtain ⟨hall, p, hpbox, hpeq, -⟩ := gerver_parameter_identification
    exact (hall p hpbox hpeq).2.2.2.2.2.2.2.1
  have := Real.pi_gt_three
  linarith

/-! ### The stage times as certified angles

`gerverStageTimes` is defined from the paper angles `GerversSofa.φ` and `GerversSofa.θ`,
while the certified Part C geometry is indexed by the vendor parameter fields
`params.phi`, `params.theta` and the derived angles `eta`, `tau`, `T`.  The six lemmas
below are the dictionary between the two indexings; they are the only place where
`gerver_parameter_identification` is needed to see a stage time. -/

/-- The zeroth stage time is the start of the rotation interval. -/
theorem gerverStageTimes_zero : gerverStageTimes 0 = 0 := rfl

/-- The first stage time is the certified first switching angle `params.phi`. -/
theorem gerverStageTimes_one : gerverStageTimes 1 = GerverSofa.PartC.params.phi := by
  obtain ⟨-, hphi, -⟩ := gerver_parameter_identification.1 GerverSofa.PartB.params
    GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  simp [gerverStageTimes, hphi.trans selected_phi]

/-- The second stage time is the certified second switching angle `params.theta`. -/
theorem gerverStageTimes_two : gerverStageTimes 2 = GerverSofa.PartC.params.theta := by
  obtain ⟨-, -, htheta, -⟩ := gerver_parameter_identification.1 GerverSofa.PartB.params
    GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  simp [gerverStageTimes, htheta.trans selected_theta]

/-- The third stage time is the certified reflected angle `eta = T - params.theta`. -/
theorem gerverStageTimes_three : gerverStageTimes 3 = GerverSofa.PartC.eta := by
  have h := gerverStageTimes_two
  simp only [gerverStageTimes, Matrix.cons_val] at h ⊢
  rw [GerverSofa.PartC.eta, GerverSofa.PartC.T, ← h]

/-- The fourth stage time is the certified reflected angle `tau = T - params.phi`. -/
theorem gerverStageTimes_four : gerverStageTimes 4 = GerverSofa.PartC.tau := by
  have h := gerverStageTimes_one
  simp only [gerverStageTimes, Matrix.cons_val] at h ⊢
  rw [GerverSofa.PartC.tau, GerverSofa.PartC.T, ← h]

/-- The fifth stage time is the certified end `T` of the rotation interval. -/
theorem gerverStageTimes_five : gerverStageTimes 5 = GerverSofa.PartC.T := rfl

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Gerver / Contacts
-/

public section

noncomputable section

open scoped ContDiff

namespace MovingSofa

/-- Resolve the Gerver path derivative into its normal and tangent frame components. -/
@[expose]
def paperGerverVelocityComponents (t : ℝ) : ℝ × ℝ :=
  (inner ℝ (deriv paperGerverPath t) (normalVector (t : Real.Angle)),
    inner ℝ (deriv paperGerverPath t) (tangentVector (t : Real.Angle)))

/-- The four standard support-contact points determined by the Gerver path and its derivative. -/
@[expose]
def paperGerverContacts (t : ℝ) : Fin 4 → Point :=
  ![paperGerverPath t + (paperGerverVelocityComponents t).1 • tangentVector (t : Real.Angle) +
      normalVector (t : Real.Angle),
    paperGerverPath t + (paperGerverVelocityComponents t).1 • tangentVector (t : Real.Angle),
    paperGerverPath t - (paperGerverVelocityComponents t).2 • normalVector (t : Real.Angle) +
      tangentVector (t : Real.Angle),
    paperGerverPath t - (paperGerverVelocityComponents t).2 • normalVector (t : Real.Angle)]

/-- Bundle the path velocity components and the four contact curves. -/
def paperGerverContactData : (ℝ → ℝ × ℝ) × (ℝ → Fin 4 → Point) :=
  (paperGerverVelocityComponents, paperGerverContacts)

/-- The explicit body-frame velocity coefficients on a selected Romik branch. -/
@[expose]
def gerverBranchVelocityComponents (i : Fin 5) (t : ℝ) : ℝ × ℝ :=
  ![GerverSofa.Romik.alphaBeta1 GerverSofa.PartB.params t,
    GerverSofa.Romik.alphaBeta2 GerverSofa.PartB.params t,
    GerverSofa.Romik.alphaBeta3 GerverSofa.PartB.params t,
    GerverSofa.Romik.alphaBeta4 GerverSofa.PartB.params t,
    GerverSofa.Romik.alphaBeta5 GerverSofa.PartB.params t] i

/-! ### The common shape of the four contact curves

`paperGerverContacts` is an instance of a generic four-slot shape built from a base curve
and two scalar coefficient functions.  Continuity and smoothness of the shape are proved
once here and reused for the ambient curve and for each analytic stage branch. -/

/-- The four contact curves are continuous as soon as the base curve and the two
coefficient functions are. -/
private theorem continuous_contactShape (X : ℝ → Point) (A B : ℝ → ℝ) (hX : Continuous X)
    (hA : Continuous A) (hB : Continuous B) :
    Continuous fun t : ℝ => (![
      X t + A t • tangentVector (t : Real.Angle) + normalVector (t : Real.Angle),
      X t + A t • tangentVector (t : Real.Angle),
      X t - B t • normalVector (t : Real.Angle) + tangentVector (t : Real.Angle),
      X t - B t • normalVector (t : Real.Angle)] : Fin 4 → Point) := by
  have hN : Continuous fun t : ℝ => normalVector (t : Real.Angle) :=
    contDiff_normalVector.continuous
  have hT : Continuous fun t : ℝ => tangentVector (t : Real.Angle) :=
    contDiff_tangentVector.continuous
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact (hX.add (hA.smul hT)).add hN
  · exact hX.add (hA.smul hT)
  · exact (hX.sub (hB.smul hN)).add hT
  · exact hX.sub (hB.smul hN)

/-- The four contact curves are smooth as soon as the base curve and the two coefficient
functions are. -/
private theorem contDiff_contactShape (X : ℝ → Point) (A B : ℝ → ℝ)
    (hX : ContDiff ℝ ∞ X) (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ fun t : ℝ => (![
      X t + A t • tangentVector (t : Real.Angle) + normalVector (t : Real.Angle),
      X t + A t • tangentVector (t : Real.Angle),
      X t - B t • normalVector (t : Real.Angle) + tangentVector (t : Real.Angle),
      X t - B t • normalVector (t : Real.Angle)] : Fin 4 → Point) := by
  rw [contDiff_pi]
  intro i
  fin_cases i
  · exact (hX.add (hA.smul contDiff_tangentVector)).add contDiff_normalVector
  · exact hX.add (hA.smul contDiff_tangentVector)
  · exact (hX.sub (hB.smul contDiff_normalVector)).add contDiff_tangentVector
  · exact hX.sub (hB.smul contDiff_normalVector)

open GerverSofa.Romik GerverSofa.PartF.Coordinates in
theorem paperGerverContactData_properties :
    Continuous paperGerverVelocityComponents ∧ Continuous paperGerverContacts ∧
    (∀ i : Fin 5, ContDiffOn ℝ ∞ paperGerverContacts (gerverStageIntervals i)) ∧
    (∀ i : Fin 5, ∀ t ∈ gerverStageIntervals i,
      paperGerverVelocityComponents t = gerverBranchVelocityComponents i t) := by
  -- Abbreviate the certified direct parameter vector, and order its switching angles.
  obtain ⟨p, hp⟩ : ∃ p : Params, GerverSofa.PartB.params = p := ⟨_, rfl⟩
  have hmem : p ∈ gerverDirectBox := hp ▸ GerverSofa.PartB.params_mem
  have heqs : gerverDirectEquations p := hp ▸ GerverSofa.PartB.params_equations
  obtain ⟨hC1, -, -⟩ := gerver_direct_path_regularity p hmem heqs
  obtain ⟨-, hphi, htheta, hphipos, hphitheta, hthetalt, -⟩ :=
    gerver_parameter_identification.1 p hmem heqs
  have hphi' : p.phi = GerversSofa.φ := hphi.trans selected_phi
  have htheta' : p.theta = GerversSofa.θ := htheta.trans selected_theta
  have h0 : (0 : ℝ) < p.phi := by rw [hphi]; exact hphipos
  have h1 : p.phi < p.theta := by rw [hphi, htheta]; exact hphitheta
  have h2 : p.theta < Real.pi / 4 := by rw [htheta]; exact hthetalt
  have hC1' : ContDiff ℝ 1 (path GerverSofa.PartB.params) := by rw [hp]; exact hC1
  -- The velocity components read off the body-frame derivative of the direct path.
  have hvel : ∀ (w : GerverSofa.Point) (t : ℝ), deriv (path p) t = rot t w →
      paperGerverVelocityComponents t = w := by
    intro w t hw
    have hd : deriv paperGerverPath t = toPlane (rot t w) := by
      rw [deriv_paperGerverPath hC1' t, hp, hw]
    simp only [paperGerverVelocityComponents, hd, inner_toPlane_rot_normalVector,
      inner_toPlane_rot_tangentVector]
  have hvelC : Continuous paperGerverVelocityComponents :=
    ((continuous_deriv_paperGerverPath hC1').inner contDiff_normalVector.continuous).prodMk
      ((continuous_deriv_paperGerverPath hC1').inner contDiff_tangentVector.continuous)
  -- Stage smoothness: the contacts agree there with the smooth analytic branch data.
  have hstage : ∀ (X W : ℝ → GerverSofa.Point) (s : Set ℝ), ContDiff ℝ ∞ X →
      ContDiff ℝ ∞ W → (∀ t ∈ s, path p t = X t) →
      (∀ t ∈ s, deriv (path p) t = rot t (W t)) →
      ContDiffOn ℝ ∞ paperGerverContacts s := by
    intro X W s hX hW hXe hWe
    refine (contDiff_contactShape (fun t => toPlane (X t)) (fun t => (W t).1)
      (fun t => (W t).2) (contDiff_toPlane hX) hW.fst hW.snd).contDiffOn.congr ?_
    intro t ht
    have hx : paperGerverPath t = toPlane (X t) := by
      change toPlane (path GerverSofa.PartB.params t) = toPlane (X t)
      rw [hp]
      exact congrArg toPlane (hXe t ht)
    simp only [paperGerverContacts, hx, hvel (W t) t (hWe t ht)]
  -- The five stage intervals, in terms of the direct switching angles.
  have hI0 : gerverStageIntervals 0 = Set.Icc 0 p.phi := by
    simp [gerverStageIntervals, gerverStageTimes, hphi']
  have hI1 : gerverStageIntervals 1 = Set.Icc p.phi p.theta := by
    simp [gerverStageIntervals, gerverStageTimes, hphi', htheta']
  have hI2 : gerverStageIntervals 2 = Set.Icc p.theta (Real.pi / 2 - p.theta) := by
    simp [gerverStageIntervals, gerverStageTimes, htheta']
  have hI3 : gerverStageIntervals 3 =
      Set.Icc (Real.pi / 2 - p.theta) (Real.pi / 2 - p.phi) := by
    simp [gerverStageIntervals, gerverStageTimes, hphi', htheta']
  have hI4 : gerverStageIntervals 4 = Set.Icc (Real.pi / 2 - p.phi) (Real.pi / 2) := by
    simp [gerverStageIntervals, gerverStageTimes, hphi']
  -- The stage coefficient pairs, read off the vector of branch velocities.
  have hB0 : ∀ t, gerverBranchVelocityComponents 0 t = alphaBeta1 p t := fun t => by
    simp [gerverBranchVelocityComponents, hp]
  have hB1 : ∀ t, gerverBranchVelocityComponents 1 t = alphaBeta2 p t := fun t => by
    simp [gerverBranchVelocityComponents, hp]
  have hB2 : ∀ t, gerverBranchVelocityComponents 2 t = alphaBeta3 p t := fun t => by
    simp [gerverBranchVelocityComponents, hp]
  have hB3 : ∀ t, gerverBranchVelocityComponents 3 t = alphaBeta4 p t := fun t => by
    simp [gerverBranchVelocityComponents, hp]
  have hB4 : ∀ t, gerverBranchVelocityComponents 4 t = alphaBeta5 p t := fun t => by
    simp [gerverBranchVelocityComponents, hp]
  refine ⟨hvelC, ?_, ?_, ?_⟩
  · exact continuous_contactShape paperGerverPath
      (fun t => (paperGerverVelocityComponents t).1)
      (fun t => (paperGerverVelocityComponents t).2) (continuous_paperGerverPath hC1')
      hvelC.fst hvelC.snd
  · intro i
    fin_cases i
    · exact hstage (path1 p) (alphaBeta1 p) (gerverStageIntervals 0) (contDiff_path1 p)
        (contDiff_alphaBeta1 p) (fun t ht => path_eq_path1_of_mem_Icc p (hI0 ▸ ht))
        (fun t ht => deriv_path_eq_rot_alphaBeta1 hC1 h0 (hI0 ▸ ht))
    · exact hstage (path2 p) (alphaBeta2 p) (gerverStageIntervals 1) (contDiff_path2 p)
        (contDiff_alphaBeta2 p) (fun t ht => path_eq_path2_of_mem_Icc heqs (hI1 ▸ ht))
        (fun t ht => deriv_path_eq_rot_alphaBeta2 hC1 heqs h1 (hI1 ▸ ht))
    · exact hstage (path3 p) (alphaBeta3 p) (gerverStageIntervals 2) (contDiff_path3 p)
        (contDiff_alphaBeta3 p) (fun t ht => path_eq_path3_of_mem_Icc heqs h1 (hI2 ▸ ht))
        (fun t ht => deriv_path_eq_rot_alphaBeta3 hC1 heqs h1 h2 (hI2 ▸ ht))
    · exact hstage (path4 p) (alphaBeta4 p) (gerverStageIntervals 3) (contDiff_path4 p)
        (contDiff_alphaBeta4 p) (fun t ht => path_eq_path4_of_mem_Icc heqs h1 h2 (hI3 ▸ ht))
        (fun t ht => deriv_path_eq_rot_alphaBeta4 hC1 heqs h1 h2 (hI3 ▸ ht))
    · exact hstage (path5 p) (alphaBeta5 p) (gerverStageIntervals 4) (contDiff_path5 p)
        (contDiff_alphaBeta5 p) (fun t ht => path_eq_path5_of_mem_Icc heqs h1 h2 (hI4 ▸ ht))
        (fun t ht => deriv_path_eq_rot_alphaBeta5 hC1 heqs h0 h1 h2 (hI4 ▸ ht))
  · intro i
    fin_cases i
    · exact fun t ht => (hvel _ t (deriv_path_eq_rot_alphaBeta1 hC1 h0
        (hI0 ▸ (ht : t ∈ gerverStageIntervals 0)))).trans (hB0 t).symm
    · exact fun t ht => (hvel _ t (deriv_path_eq_rot_alphaBeta2 hC1 heqs h1
        (hI1 ▸ (ht : t ∈ gerverStageIntervals 1)))).trans (hB1 t).symm
    · exact fun t ht => (hvel _ t (deriv_path_eq_rot_alphaBeta3 hC1 heqs h1 h2
        (hI2 ▸ (ht : t ∈ gerverStageIntervals 2)))).trans (hB2 t).symm
    · exact fun t ht => (hvel _ t (deriv_path_eq_rot_alphaBeta4 hC1 heqs h1 h2
        (hI3 ▸ (ht : t ∈ gerverStageIntervals 3)))).trans (hB3 t).symm
    · exact fun t ht => (hvel _ t (deriv_path_eq_rot_alphaBeta5 hC1 heqs h0 h1 h2
        (hI4 ▸ (ht : t ∈ gerverStageIntervals 4)))).trans (hB4 t).symm

/-! ### Identification with the certified piecewise contact data -/

/-- On the physical rotation interval the paper velocity components agree with the vendor
piecewise body-frame coefficients. -/
theorem paperGerverVelocityComponents_eq_alphaBetaAt (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    paperGerverVelocityComponents t = GerverSofa.PartC.alphaBetaAt t := by
  obtain ⟨-, hphi, htheta, -⟩ := gerver_parameter_identification.1 GerverSofa.PartB.params
    GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  have hphi' : GerverSofa.PartB.params.phi = GerversSofa.φ := hphi.trans selected_phi
  have htheta' : GerverSofa.PartB.params.theta = GerversSofa.θ := htheta.trans selected_theta
  have hvel := paperGerverContactData_properties.2.2.2
  have hI0 : gerverStageIntervals 0 = Set.Icc 0 GerversSofa.φ := by
    simp [gerverStageIntervals, gerverStageTimes]
  have hI1 : gerverStageIntervals 1 = Set.Icc GerversSofa.φ GerversSofa.θ := by
    simp [gerverStageIntervals, gerverStageTimes]
  have hI2 : gerverStageIntervals 2 = Set.Icc GerversSofa.θ (Real.pi / 2 - GerversSofa.θ) := by
    simp [gerverStageIntervals, gerverStageTimes]
  have hI3 : gerverStageIntervals 3 =
      Set.Icc (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ) := by
    simp [gerverStageIntervals, gerverStageTimes]
  have hI4 : gerverStageIntervals 4 = Set.Icc (Real.pi / 2 - GerversSofa.φ) (Real.pi / 2) := by
    simp [gerverStageIntervals, gerverStageTimes]
  obtain ⟨ht0, ht2⟩ := ht
  simp only [GerverSofa.PartC.alphaBetaAt, GerverSofa.PartC.eta, GerverSofa.PartC.tau,
    GerverSofa.PartC.T, hphi', htheta']
  split_ifs with h1 h2 h3 h4
  · have := hvel 0 t (by rw [hI0]; exact ⟨ht0, h1⟩)
    simpa [gerverBranchVelocityComponents] using this
  · have := hvel 1 t (by rw [hI1]; exact ⟨le_of_not_ge h1, h2⟩)
    simpa [gerverBranchVelocityComponents] using this
  · have := hvel 2 t (by rw [hI2]; exact ⟨le_of_not_ge h2, h3⟩)
    simpa [gerverBranchVelocityComponents] using this
  · have := hvel 3 t (by rw [hI3]; exact ⟨le_of_not_ge h3, h4⟩)
    simpa [gerverBranchVelocityComponents] using this
  · have := hvel 4 t (by rw [hI4]; exact ⟨le_of_not_ge h4, ht2⟩)
    simpa [gerverBranchVelocityComponents] using this

/-- On the physical rotation interval the four paper contact curves are the coordinate
transports of the four certified contact curves. -/
theorem fromPlane_paperGerverContacts (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (i : Fin 4) :
    GerverSofa.PartF.Coordinates.fromPlane (paperGerverContacts t i) =
      ![GerverSofa.PartC.A t, GerverSofa.PartC.B t, GerverSofa.PartC.C t,
        GerverSofa.PartC.D t] i := by
  have hab := paperGerverVelocityComponents_eq_alphaBetaAt t ht
  fin_cases i <;> simp only [paperGerverContacts, hab] <;> rfl

/-- On the physical rotation interval the second paper contact curve is the certified curve
`B`, read in plane coordinates. -/
theorem paperGerverContacts_one_eq_toPlane {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    paperGerverContacts t 1 =
      GerverSofa.PartF.Coordinates.toPlane (GerverSofa.PartC.B t) :=
  (GerverSofa.PartF.Coordinates.toPlane_fromPlane _).symm.trans
    (congrArg GerverSofa.PartF.Coordinates.toPlane (fromPlane_paperGerverContacts t ht 1))

/-- On the physical rotation interval the fourth paper contact curve is the certified curve
`D`, read in plane coordinates. -/
theorem paperGerverContacts_three_eq_toPlane {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    paperGerverContacts t 3 =
      GerverSofa.PartF.Coordinates.toPlane (GerverSofa.PartC.D t) :=
  (GerverSofa.PartF.Coordinates.toPlane_fromPlane _).symm.trans
    (congrArg GerverSofa.PartF.Coordinates.toPlane (fromPlane_paperGerverContacts t ht 3))

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The Gerver niche roof

The upper boundary of the paper's literal Gerver niche is a three-piece graph over the
rotation interval: the fourth contact curve up to the second stage time, the direct path run
*backwards* through the affine reversal `gerverRoofReverseTime` on the middle stage, and the
second contact curve from the third stage time on.  `gerverRoofCurve` is that graph as a
function of an unrestricted real parameter and `gerverNicheRoof` its restriction to the
rotation interval; `gerverRoofCurve_eq` relates the two.
-/

public section

noncomputable section

namespace MovingSofa

/-- The affine reversal of the middle roof stage: it maps `gerverStageTimes 2` to
`gerverStageTimes 4` and `gerverStageTimes 3` to `gerverStageTimes 1`, so it reparametrizes
the central part of the direct path backwards. -/
@[expose]
def gerverRoofReverseTime (s : ℝ) : ℝ :=
  gerverStageTimes 4 - (gerverStageTimes 4 - gerverStageTimes 1) /
    (gerverStageTimes 3 - gerverStageTimes 2) * (s - gerverStageTimes 2)

/-- The Gerver niche roof as a curve of an unrestricted real parameter.  On the rotation
interval it agrees with `gerverNicheRoof` (`gerverRoofCurve_eq`); the unrestricted form is
what the intermediate value theorem and `continuous_if_le` consume. -/
@[expose]
def gerverRoofCurve (s : ℝ) : Point :=
  if s ≤ gerverStageTimes 2 then paperGerverContacts s 3
  else if s ≤ gerverStageTimes 3 then paperGerverPath (gerverRoofReverseTime s)
  else paperGerverContacts s 1

/-- The three-branch roof of the Gerver niche, using two contact arcs and the reversed path. -/
@[expose]
def gerverNicheRoof (s : Set.Icc (0 : ℝ) (Real.pi / 2)) : Point :=
  if s.val ≤ gerverStageTimes 2 then paperGerverContacts s.val 3
  else if s.val ≤ gerverStageTimes 3 then paperGerverPath (gerverRoofReverseTime s.val)
  else paperGerverContacts s.val 1

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Gerver / ODEs
-/

public section

noncomputable section

namespace MovingSofa

/-- Tangential components of the four contact-curve derivatives on a selected stage. -/
@[expose]
def gerverStageContactDerivatives (i : Fin 5) (t : ℝ) : Fin 4 → ℝ :=
  ![inner ℝ (derivWithin (fun s ↦ paperGerverContacts s 0) (gerverStageIntervals i) t)
      (tangentVector (t : Real.Angle)),
    inner ℝ (derivWithin (fun s ↦ paperGerverContacts s 1) (gerverStageIntervals i) t)
      (tangentVector (t : Real.Angle)),
    inner ℝ (-(derivWithin (fun s ↦ paperGerverContacts s 2) (gerverStageIntervals i) t))
      (normalVector (t : Real.Angle)),
    inner ℝ (derivWithin (fun s ↦ paperGerverContacts s 3) (gerverStageIntervals i) t)
      (normalVector (t : Real.Angle))]

private theorem gerver_contact_derivatives_from_frame (i : Fin 5) (t : ℝ)
    (ht : t ∈ gerverStageIntervals i)
    (huniq : UniqueDiffWithinAt ℝ (gerverStageIntervals i) t) :
    ∀ (X : ℝ → Point) (X' : Point) (A B : ℝ → ℝ) (a' b' : ℝ),
     HasDerivAt X X' t →
     inner ℝ X' (normalVector (t : Real.Angle)) = A t →
     inner ℝ X' (tangentVector (t : Real.Angle)) = B t →
     HasDerivAt A a' t → HasDerivAt B b' t →
     (∀ r ∈ gerverStageIntervals i, paperGerverPath r = X r) →
     (∀ r ∈ gerverStageIntervals i, paperGerverVelocityComponents r = (A r, B r)) →
     gerverStageContactDerivatives i t 0 = B t + a' + 1 ∧
     gerverStageContactDerivatives i t 1 = B t + a' ∧
     gerverStageContactDerivatives i t 2 = b' + 1 - A t ∧
     gerverStageContactDerivatives i t 3 = A t - b' := by
  -- Frame orthonormality at the fixed angle `t`.
  have huu :
      inner ℝ (normalVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = (1 : ℝ) :=
    inner_normalVector_self t
  have hvv :
      inner ℝ (tangentVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = (1 : ℝ) :=
    inner_tangentVector_self t
  have huv :
      inner ℝ (normalVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = (0 : ℝ) :=
    inner_normalVector_tangentVector t
  have hvu :
      inner ℝ (tangentVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = (0 : ℝ) := by
    rw [real_inner_comm]; exact huv
  intro X X' A B a' b' hX hXu hXv hA hB hpath hvel
  have hn : HasDerivAt (fun s : ℝ => normalVector (s : Real.Angle))
      (tangentVector (t : Real.Angle)) t := hasDerivAt_normalVector t
  have hg : HasDerivAt (fun s : ℝ => tangentVector (s : Real.Angle))
      (-normalVector (t : Real.Angle)) t := hasDerivAt_tangentVector t
  have hAv := hA.fun_smul hg
  have hBn := hB.fun_smul hn
  have hc0 : HasDerivWithinAt (fun s => paperGerverContacts s 0)
      (X' + (A t • (-normalVector (t : Real.Angle)) + a' • tangentVector (t : Real.Angle)) +
        tangentVector (t : Real.Angle)) (gerverStageIntervals i) t := by
    refine ((hX.fun_add hAv).fun_add hn).hasDerivWithinAt.congr (fun r hr => ?_) ?_
    · simp only [paperGerverContacts, Matrix.cons_val_zero, hpath r hr, hvel r hr]
    · simp only [paperGerverContacts, Matrix.cons_val_zero, hpath t ht, hvel t ht]
  have hc1 : HasDerivWithinAt (fun s => paperGerverContacts s 1)
      (X' + (A t • (-normalVector (t : Real.Angle)) + a' • tangentVector (t : Real.Angle)))
      (gerverStageIntervals i) t := by
    refine (hX.fun_add hAv).hasDerivWithinAt.congr (fun r hr => ?_) ?_
    · simp only [paperGerverContacts, hpath r hr, hvel r hr]
      rfl
    · simp only [paperGerverContacts, hpath t ht, hvel t ht]
      rfl
  have hc2 : HasDerivWithinAt (fun s => paperGerverContacts s 2)
      (X' - (B t • tangentVector (t : Real.Angle) + b' • normalVector (t : Real.Angle)) +
        -normalVector (t : Real.Angle)) (gerverStageIntervals i) t := by
    refine ((hX.fun_sub hBn).fun_add hg).hasDerivWithinAt.congr (fun r hr => ?_) ?_
    · simp only [paperGerverContacts, hpath r hr, hvel r hr]
      rfl
    · simp only [paperGerverContacts, hpath t ht, hvel t ht]
      rfl
  have hc3 : HasDerivWithinAt (fun s => paperGerverContacts s 3)
      (X' - (B t • tangentVector (t : Real.Angle) + b' • normalVector (t : Real.Angle)))
      (gerverStageIntervals i) t := by
    refine (hX.fun_sub hBn).hasDerivWithinAt.congr (fun r hr => ?_) ?_
    · simp only [paperGerverContacts, hpath r hr, hvel r hr]
      rfl
    · simp only [paperGerverContacts, hpath t ht, hvel t ht]
      rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · change inner ℝ (derivWithin (fun s => paperGerverContacts s 0) (gerverStageIntervals i) t)
      (tangentVector (t : Real.Angle)) = B t + a' + 1
    rw [hc0.derivWithin huniq]
    simp only [inner_add_left, real_inner_smul_left, inner_neg_left, hXv, huv, hvv]
    ring
  · change inner ℝ (derivWithin (fun s => paperGerverContacts s 1) (gerverStageIntervals i) t)
      (tangentVector (t : Real.Angle)) = B t + a'
    rw [hc1.derivWithin huniq]
    simp only [inner_add_left, real_inner_smul_left, inner_neg_left, hXv, huv, hvv]
    ring
  · change inner ℝ (-derivWithin (fun s => paperGerverContacts s 2) (gerverStageIntervals i) t)
      (normalVector (t : Real.Angle)) = b' + 1 - A t
    rw [hc2.derivWithin huniq]
    simp only [inner_neg_left, inner_add_left, inner_sub_left, real_inner_smul_left, hXu, hvu,
      huu]
    ring
  · change inner ℝ (derivWithin (fun s => paperGerverContacts s 3) (gerverStageIntervals i) t)
      (normalVector (t : Real.Angle)) = A t - b'
    rw [hc3.derivWithin huniq]
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left, hXu, hvu, huu]
    ring

theorem gerver_stageODEs (i : Fin 5) (t : ℝ) (ht : t ∈ gerverStageIntervals i) :
    (gerverStageContactDerivatives i t 0, gerverStageContactDerivatives i t 2) =
      ![(0, gerverStageContactDerivatives i t 3),
        ((paperGerverVelocityComponents t).2,
          gerverStageContactDerivatives i t 3 - (paperGerverVelocityComponents t).1),
        ((paperGerverVelocityComponents t).2, -(paperGerverVelocityComponents t).1),
        (-gerverStageContactDerivatives i t 1 + (paperGerverVelocityComponents t).2,
          -(paperGerverVelocityComponents t).1),
        (-gerverStageContactDerivatives i t 1, 0)] i := by
  open GerverSofa.Romik GerverSofa.PartF.Coordinates in
  -- The certified direct parameter vector and the ordering of its switching angles.
  obtain ⟨p, hp⟩ : ∃ p : Params, GerverSofa.PartB.params = p := ⟨_, rfl⟩
  have hmem : p ∈ gerverDirectBox := hp ▸ GerverSofa.PartB.params_mem
  have heqs : gerverDirectEquations p := hp ▸ GerverSofa.PartB.params_equations
  obtain ⟨-, hphieq, hthetaeq, hphipos, hphitheta, hthetalt, -⟩ :=
    gerver_parameter_identification.1 p hmem heqs
  have hphi' : p.phi = GerversSofa.φ := hphieq.trans selected_phi
  have htheta' : p.theta = GerversSofa.θ := hthetaeq.trans selected_theta
  have h0 : (0 : ℝ) < p.phi := by rw [hphieq]; exact hphipos
  have h1 : p.phi < p.theta := by rw [hphieq, hthetaeq]; exact hphitheta
  have h2 : p.theta < Real.pi / 4 := by rw [hthetaeq]; exact hthetalt
  -- The five closed stage intervals in terms of the direct switching angles.
  have hI0 : gerverStageIntervals 0 = Set.Icc 0 p.phi := by
    simp [gerverStageIntervals, gerverStageTimes, hphi']
  have hI1 : gerverStageIntervals 1 = Set.Icc p.phi p.theta := by
    simp [gerverStageIntervals, gerverStageTimes, hphi', htheta']
  have hI2 : gerverStageIntervals 2 = Set.Icc p.theta (Real.pi / 2 - p.theta) := by
    simp [gerverStageIntervals, gerverStageTimes, htheta']
  have hI3 : gerverStageIntervals 3 =
      Set.Icc (Real.pi / 2 - p.theta) (Real.pi / 2 - p.phi) := by
    simp [gerverStageIntervals, gerverStageTimes, hphi', htheta']
  have hI4 : gerverStageIntervals 4 = Set.Icc (Real.pi / 2 - p.phi) (Real.pi / 2) := by
    simp [gerverStageIntervals, gerverStageTimes, hphi']
  have hval := paperGerverContactData_properties.2.2.2
  -- Derivatives of the ten branch coefficient functions, in one normal form.
  have hidt : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have hshape : ∀ (c₀ c₁ c₂ c₃ c₄ : ℝ) (f : ℝ → ℝ),
      (∀ s : ℝ,
        f s = c₀ + c₁ * s + c₂ * s * s + c₃ * Real.sin s + c₄ * Real.cos s) →
      HasDerivAt f (c₁ + 2 * c₂ * t + c₃ * Real.cos t - c₄ * Real.sin t) t := by
    intro c₀ c₁ c₂ c₃ c₄ f hf
    have h : HasDerivAt
        (fun s : ℝ => c₀ + c₁ * s + c₂ * s * s + c₃ * Real.sin s + c₄ * Real.cos s)
        (c₁ + 2 * c₂ * t + c₃ * Real.cos t - c₄ * Real.sin t) t := by
      refine ((((hasDerivAt_const t c₀).fun_add (hidt.const_mul c₁)).fun_add
        ((hidt.const_mul c₂).fun_mul hidt)).fun_add
        ((Real.hasDerivAt_sin t).const_mul c₃)).fun_add
        ((Real.hasDerivAt_cos t).const_mul c₄) |>.congr_deriv ?_
      ring
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => hf s)
  -- Unique differentiability of the closed stage interval at `t`.
  have g0 : (0 : ℝ) < GerversSofa.φ := by rw [← hphi']; exact h0
  have g1 : GerversSofa.φ < GerversSofa.θ := by rw [← hphi', ← htheta']; exact h1
  have g2 : GerversSofa.θ < Real.pi / 4 := by rw [← htheta']; exact h2
  have huniq : UniqueDiffWithinAt ℝ (gerverStageIntervals i) t := by
    fin_cases i
    · exact uniqueDiffOn_Icc g0 t ht
    · exact uniqueDiffOn_Icc g1 t ht
    · exact uniqueDiffOn_Icc
        (show GerversSofa.θ < Real.pi / 2 - GerversSofa.θ by linarith) t ht
    · exact uniqueDiffOn_Icc
        (show Real.pi / 2 - GerversSofa.θ < Real.pi / 2 - GerversSofa.φ by linarith) t ht
    · exact uniqueDiffOn_Icc
        (show Real.pi / 2 - GerversSofa.φ < Real.pi / 2 by linarith) t ht
  -- The frame computation: the four contact derivatives in terms of `α, β, α', β'`.
  have hcore := gerver_contact_derivatives_from_frame i t ht huniq
  fin_cases i
  · -- Stage 1
    have hvel : ∀ r ∈ gerverStageIntervals 0,
        paperGerverVelocityComponents r = alphaBeta1 p r := by
      intro r hr
      rw [hval 0 r hr]
      simp [gerverBranchVelocityComponents, hp]
    obtain ⟨e0, e1, e2, e3⟩ := hcore (fun s => toPlane (path1 p s))
      (toPlane (rot t (alphaBeta1 p t))) (fun s => (alphaBeta1 p s).1)
      (fun s => (alphaBeta1 p s).2) _ _ (hasDerivAt_toPlane (hasDerivAt_path1 p t))
      (inner_toPlane_rot_normalVector t _) (inner_toPlane_rot_tangentVector t _)
      (hshape (1 / 2) 0 0 (-2 * p.a1) (2 * p.a2) _ fun s => by dsimp [alphaBeta1]; ring)
      (hshape (-1) 0 0 (2 * p.a2) (2 * p.a1) _ fun s => by dsimp [alphaBeta1]; ring)
      (fun r hr => by
        change toPlane (path GerverSofa.PartB.params r) = toPlane (path1 p r)
        rw [hp]
        exact congrArg toPlane (path_eq_path1_of_mem_Icc p (hI0 ▸ hr)))
      (fun r hr => hvel r hr)
    rw [Prod.mk.injEq, e0, e2, e3]
    refine ⟨?_, ?_⟩ <;> dsimp [alphaBeta1] <;> ring
  · -- Stage 2
    have hvel : ∀ r ∈ gerverStageIntervals 1,
        paperGerverVelocityComponents r = alphaBeta2 p r := by
      intro r hr
      rw [hval 1 r hr]
      simp [gerverBranchVelocityComponents, hp]
    obtain ⟨e0, e1, e2, e3⟩ := hcore (fun s => toPlane (path2 p s))
      (toPlane (rot t (alphaBeta2 p t))) (fun s => (alphaBeta2 p s).1)
      (fun s => (alphaBeta2 p s).2) _ _ (hasDerivAt_toPlane (hasDerivAt_path2 p t))
      (inner_toPlane_rot_normalVector t _) (inner_toPlane_rot_tangentVector t _)
      (hshape (1 + 2 * p.b1) (-1) 0 0 0 _ fun s => by dsimp [alphaBeta2]; ring)
      (hshape (p.b2 + 1 / 2) p.b1 (-(1 / 4)) 0 0 _ fun s => by dsimp [alphaBeta2]; ring)
      (fun r hr => by
        change toPlane (path GerverSofa.PartB.params r) = toPlane (path2 p r)
        rw [hp]
        exact congrArg toPlane (path_eq_path2_of_mem_Icc heqs (hI1 ▸ hr)))
      (fun r hr => hvel r hr)
    rw [Prod.mk.injEq, hvel t ht, e0, e2, e3]
    refine ⟨?_, ?_⟩ <;> dsimp [alphaBeta2] <;> ring
  · -- Stage 3
    have hvel : ∀ r ∈ gerverStageIntervals 2,
        paperGerverVelocityComponents r = alphaBeta3 p r := by
      intro r hr
      rw [hval 2 r hr]
      simp [gerverBranchVelocityComponents, hp]
    obtain ⟨e0, e1, e2, e3⟩ := hcore (fun s => toPlane (path3 p s))
      (toPlane (rot t (alphaBeta3 p t))) (fun s => (alphaBeta3 p s).1)
      (fun s => (alphaBeta3 p s).2) _ _ (hasDerivAt_toPlane (hasDerivAt_path3 p t))
      (inner_toPlane_rot_normalVector t _) (inner_toPlane_rot_tangentVector t _)
      (hshape (-1 - p.c2) (-1) 0 0 0 _ fun s => by dsimp [alphaBeta3]; ring)
      (hshape (1 + p.c1) (-1) 0 0 0 _ fun s => by dsimp [alphaBeta3]; ring)
      (fun r hr => by
        change toPlane (path GerverSofa.PartB.params r) = toPlane (path3 p r)
        rw [hp]
        exact congrArg toPlane (path_eq_path3_of_mem_Icc heqs h1 (hI2 ▸ hr)))
      (fun r hr => hvel r hr)
    rw [Prod.mk.injEq, hvel t ht, e0, e2]
    refine ⟨?_, ?_⟩ <;> dsimp [alphaBeta3] <;> ring
  · -- Stage 4
    have hvel : ∀ r ∈ gerverStageIntervals 3,
        paperGerverVelocityComponents r = alphaBeta4 p r := by
      intro r hr
      rw [hval 3 r hr]
      simp [gerverBranchVelocityComponents, hp]
    obtain ⟨e0, e1, e2, e3⟩ := hcore (fun s => toPlane (path4 p s))
      (toPlane (rot t (alphaBeta4 p t))) (fun s => (alphaBeta4 p s).1)
      (fun s => (alphaBeta4 p s).2) _ _ (hasDerivAt_toPlane (hasDerivAt_path4 p t))
      (inner_toPlane_rot_normalVector t _) (inner_toPlane_rot_tangentVector t _)
      (hshape (-p.d2 - 1 / 2) (-p.d1) (1 / 4) 0 0 _ fun s => by dsimp [alphaBeta4]; ring)
      (hshape (2 * p.d1 - 1) (-1) 0 0 0 _ fun s => by dsimp [alphaBeta4]; ring)
      (fun r hr => by
        change toPlane (path GerverSofa.PartB.params r) = toPlane (path4 p r)
        rw [hp]
        exact congrArg toPlane (path_eq_path4_of_mem_Icc heqs h1 h2 (hI3 ▸ hr)))
      (fun r hr => hvel r hr)
    rw [Prod.mk.injEq, hvel t ht, e0, e1, e2]
    refine ⟨?_, ?_⟩ <;> dsimp [alphaBeta4] <;> ring
  · -- Stage 5
    have hvel : ∀ r ∈ gerverStageIntervals 4,
        paperGerverVelocityComponents r = alphaBeta5 p r := by
      intro r hr
      rw [hval 4 r hr]
      simp [gerverBranchVelocityComponents, hp]
    obtain ⟨e0, e1, e2, e3⟩ := hcore (fun s => toPlane (path5 p s))
      (toPlane (rot t (alphaBeta5 p t))) (fun s => (alphaBeta5 p s).1)
      (fun s => (alphaBeta5 p s).2) _ _ (hasDerivAt_toPlane (hasDerivAt_path5 p t))
      (inner_toPlane_rot_normalVector t _) (inner_toPlane_rot_tangentVector t _)
      (hshape 1 0 0 (-2 * p.e1) (2 * p.e2) _ fun s => by dsimp [alphaBeta5]; ring)
      (hshape (-(1 / 2)) 0 0 (2 * p.e2) (2 * p.e1) _ fun s => by dsimp [alphaBeta5]; ring)
      (fun r hr => by
        change toPlane (path GerverSofa.PartB.params r) = toPlane (path5 p r)
        rw [hp]
        exact congrArg toPlane (path_eq_path5_of_mem_Icc heqs h1 h2 (hI4 ▸ hr)))
      (fun r hr => hvel r hr)
    rw [Prod.mk.injEq, e0, e1, e2]
    refine ⟨?_, ?_⟩ <;> dsimp [alphaBeta5] <;> ring

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Gerver / Outer Contacts
-/

public section

noncomputable section

namespace MovingSofa

theorem gerver_outer_contact_A (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    paperGerverContacts t 0 ∈ gerverOuterCap := by
  rw [mem_gerverOuterCap_iff, fromPlane_paperGerverContacts t ht 0]
  exact GerverSofa.PartC.Stage3.supportA_direct t ht

theorem gerver_outer_contact_C (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    paperGerverContacts t 2 ∈ gerverOuterCap := by
  rw [mem_gerverOuterCap_iff, fromPlane_paperGerverContacts t ht 2]
  exact GerverSofa.PartC.Stage3.supportC_direct t ht

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Regularity of the certified Gerver stage data

The five Gerver stages are nondegenerate: the six stage endpoints increase strictly from `0`
to `π / 2` (`gerverStageTimes_strictMono`), and `gerverStageIntervals_zero` through
`gerverStageIntervals_four` name the resulting closed stage intervals.  The certified direct
path is continuously differentiable on the whole rotation interval
(`contDiff_paperGerverPath`), while each contact curve is only continuous globally
(`continuous_paperGerverContact`) and continuously differentiable on a single stage
(`contDiffOn_paperGerverContact`).  Gluing two consecutive stages presents the two inner
contact curves on the parameter ranges where they touch the cap as continuous paths of bounded
variation (`gerverRightContactBV`, `gerverLeftContactBV`).

The second half of the file differentiates the two inner contact curves stagewise.  Writing
the velocity components of the direct path as `(α, β)`, the contact formulas are
`B = x + α v` and `D = x - β u`, so the product rule and the frame derivatives
`hasDerivAt_normalVector`, `hasDerivAt_tangentVector` give
`B' = (β + α') v` and `D' = (α - β') u`
(`hasDerivWithinAt_paperGerverContacts_one`, `hasDerivWithinAt_paperGerverContacts_three`).
Feeding the five analytic stage branches of `paperGerverContactData_properties` into these
two lemmas yields the signs of the two speeds on the stages where they are needed
(`hasDerivWithinAt_paperGerverContacts_one_neg_smul`,
`hasDerivWithinAt_paperGerverContacts_three_pos_smul`); the two nonconstant coefficients are
signed by the coarse box bounds `gerverDirectBox_b1_lower_bound`,
`gerverDirectBox_d1_upper_bound` and `gerverStageTimes_two_le_seven_div_ten`.

The last two sections record the consequences used downstream: the frame coordinates
`s ↦ x s ⋅ u_s` and `s ↦ x s ⋅ v_s` of the direct path are differentiable with derivatives
`B ⋅ v` and `-D ⋅ u` (`hasDerivAt_inner_paperGerverPath_normalVector`,
`hasDerivAt_inner_paperGerverPath_tangentVector`), and against a fixed frame direction outside
the stage the two inner contact curves are strictly monotone on each stage
(`strictAntiOn_inner_paperGerverContacts_three`, `strictMonoOn_inner_paperGerverContacts_one`).
-/

public section

noncomputable section

namespace MovingSofa

/-- The six Gerver stage endpoints increase strictly along the rotation interval. -/
theorem gerverStageTimes_strictMono : StrictMono gerverStageTimes := by
  obtain ⟨-, -, -, hpos, hlt, hqt, -⟩ := gerver_parameter_identification.1
    GerverSofa.PartB.params GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  rw [selected_phi] at hpos
  rw [selected_phi, selected_theta] at hlt
  rw [selected_theta] at hqt
  refine Fin.strictMono_iff_lt_succ.mpr fun i ↦ ?_
  fin_cases i
  · change gerverStageTimes 0 < gerverStageTimes 1
    simp only [gerverStageTimes, Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith
  · change gerverStageTimes 1 < gerverStageTimes 2
    simp only [gerverStageTimes, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    linarith
  · change gerverStageTimes 2 < gerverStageTimes 3
    simp only [gerverStageTimes, Matrix.cons_val]
    linarith
  · change gerverStageTimes 3 < gerverStageTimes 4
    simp only [gerverStageTimes, Matrix.cons_val]
    linarith
  · change gerverStageTimes 4 < gerverStageTimes 5
    simp only [gerverStageTimes, Matrix.cons_val]
    linarith

/-- The second Gerver stage time is at most `7/10`.  This coarse bound on the certified
switching angle `θ` is what the stage speed estimates below consume. -/
theorem gerverStageTimes_two_le_seven_div_ten : gerverStageTimes 2 ≤ (7 : ℝ) / 10 := by
  have h := GerverSofa.PartB.theta_bounds.2
  rw [gerverStageTimes_two]
  norm_num at h ⊢
  linarith

/-- The first Gerver stage runs between the first two stage times. -/
theorem gerverStageIntervals_zero :
    gerverStageIntervals 0 = Set.Icc (gerverStageTimes 0) (gerverStageTimes 1) := rfl

/-- The second Gerver stage runs between the second and third stage times. -/
theorem gerverStageIntervals_one :
    gerverStageIntervals 1 = Set.Icc (gerverStageTimes 1) (gerverStageTimes 2) := rfl

/-- The fourth Gerver stage runs between the fourth and fifth stage times. -/
theorem gerverStageIntervals_three :
    gerverStageIntervals 3 = Set.Icc (gerverStageTimes 3) (gerverStageTimes 4) := rfl

/-- The fifth Gerver stage runs between the last two stage times. -/
theorem gerverStageIntervals_four :
    gerverStageIntervals 4 = Set.Icc (gerverStageTimes 4) (gerverStageTimes 5) := rfl

/-- The certified direct Gerver path is continuously differentiable. -/
theorem contDiff_paperGerverPath : ContDiff ℝ 1 paperGerverPath := by
  obtain ⟨hC1, -, -⟩ := gerver_direct_path_regularity GerverSofa.PartB.params
    GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  obtain ⟨L, hL⟩ : ∃ L : GerverSofa.Point →L[ℝ] Point,
      ⇑L = GerverSofa.PartF.Coordinates.toPlane :=
    ⟨{ toLinearMap := GerverSofa.PartF.Coordinates.linearEquiv.toLinearMap
       cont := GerverSofa.PartF.Coordinates.continuous_toPlane }, rfl⟩
  have hcomp : paperGerverPath = ⇑L ∘ GerverSofa.Romik.path GerverSofa.PartB.params := by
    rw [hL]
    rfl
  rw [hcomp]
  exact L.contDiff.comp hC1

/-- Each Gerver contact curve is continuous. -/
theorem continuous_paperGerverContact (i : Fin 4) :
    Continuous fun t : ℝ ↦ paperGerverContacts t i :=
  (continuous_apply i).comp paperGerverContactData_properties.2.1

/-- Each Gerver contact curve is continuously differentiable on each closed stage interval. -/
theorem contDiffOn_paperGerverContact (i : Fin 4) (j : Fin 5) :
    ContDiffOn ℝ 1 (fun t : ℝ ↦ paperGerverContacts t i) (gerverStageIntervals j) :=
  (contDiffOn_pi.mp (paperGerverContactData_properties.2.2.1 j) i).of_le (by norm_num)

/-! ### The two inner contact curves as bounded-variation paths -/

/-- The second Gerver contact curve, on the two stages `[t₃, t₅]` where it is an inner contact
of the cap, as a continuous path of bounded variation. -/
@[expose]
def gerverRightContactBV : ContinuousBVPaths (gerverStageTimes 3) (gerverStageTimes 5) :=
  continuousBVOfContDiffOnIccUnionIcc (fun t ↦ paperGerverContacts t 1)
    (gerverStageTimes_strictMono (show (3 : Fin 6) < 4 by decide)).le
    (gerverStageTimes_strictMono (show (4 : Fin 6) < 5 by decide)).le
    (contDiffOn_paperGerverContact 1 3) (contDiffOn_paperGerverContact 1 4)

/-- The fourth Gerver contact curve, on the two stages `[t₀, t₂]` where it is an inner contact
of the cap, as a continuous path of bounded variation. -/
@[expose]
def gerverLeftContactBV : ContinuousBVPaths (gerverStageTimes 0) (gerverStageTimes 2) :=
  continuousBVOfContDiffOnIccUnionIcc (fun t ↦ paperGerverContacts t 3)
    (gerverStageTimes_strictMono (show (0 : Fin 6) < 1 by decide)).le
    (gerverStageTimes_strictMono (show (1 : Fin 6) < 2 by decide)).le
    (contDiffOn_paperGerverContact 3 0) (contDiffOn_paperGerverContact 3 1)

/-- `gerverRightContactBV` is the second Gerver contact curve. -/
theorem gerverRightContactBV_apply (t : Set.Icc (gerverStageTimes 3) (gerverStageTimes 5)) :
    gerverRightContactBV.val t = paperGerverContacts t 1 := rfl

/-- `gerverLeftContactBV` is the fourth Gerver contact curve. -/
theorem gerverLeftContactBV_apply (t : Set.Icc (gerverStageTimes 0) (gerverStageTimes 2)) :
    gerverLeftContactBV.val t = paperGerverContacts t 3 := rfl

/-! ### Stage derivatives of the two inner contact curves -/

/-- The velocity components are the frame coordinates of the derivative of the direct path. -/
theorem deriv_paperGerverPath_eq_smul_add_smul {t a b : ℝ}
    (h : paperGerverVelocityComponents t = (a, b)) :
    deriv paperGerverPath t =
      a • normalVector (t : Real.Angle) + b • tangentVector (t : Real.Angle) := by
  have hframe := inner_normalVector_smul_add_inner_tangentVector_smul
    (deriv paperGerverPath t) (t : Real.Angle)
  rw [paperGerverVelocityComponents, Prod.mk.injEq] at h
  rw [h.1, h.2] at hframe
  exact hframe.symm

/-- On a stage where the direct path has velocity components `(α, β)`, the second contact
curve `B = x + α v` has derivative `(β + α') v`: the frame derivative `v' = -u` cancels the
normal component `α u` of `x'`, leaving the tangential component `β v` and the derivative of
the coefficient. -/
theorem hasDerivWithinAt_paperGerverContacts_one {i : Fin 5} {t c α' : ℝ} {α β : ℝ → ℝ}
    (ht : t ∈ gerverStageIntervals i) (hα : HasDerivAt α α' t)
    (hαβ : ∀ s ∈ gerverStageIntervals i, paperGerverVelocityComponents s = (α s, β s))
    (hc : β t + α' = c) :
    HasDerivWithinAt (fun s ↦ paperGerverContacts s 1)
      (c • tangentVector (t : Real.Angle)) (gerverStageIntervals i) t := by
  have hx : HasDerivAt paperGerverPath (deriv paperGerverPath t) t :=
    (contDiff_paperGerverPath.differentiable one_ne_zero t).hasDerivAt
  have hd := deriv_paperGerverPath_eq_smul_add_smul (hαβ t ht)
  have hmain : HasDerivAt (fun s ↦ paperGerverPath s + α s • tangentVector (s : Real.Angle))
      (c • tangentVector (t : Real.Angle)) t := by
    have h := hx.add (hα.smul (hasDerivAt_tangentVector t))
    rw [hd] at h
    rw [← hc]
    convert h using 1
    module
  refine hmain.hasDerivWithinAt.congr (fun y hy ↦ ?_) ?_
  · change paperGerverPath y + (paperGerverVelocityComponents y).1 •
      tangentVector (y : Real.Angle) = _
    rw [hαβ y hy]
  · change paperGerverPath t + (paperGerverVelocityComponents t).1 •
      tangentVector (t : Real.Angle) = _
    rw [hαβ t ht]

/-- On a stage where the direct path has velocity components `(α, β)`, the fourth contact
curve `D = x - β u` has derivative `(α - β') u`; see
`hasDerivWithinAt_paperGerverContacts_one` for the shape of the computation. -/
theorem hasDerivWithinAt_paperGerverContacts_three {i : Fin 5} {t c β' : ℝ} {α β : ℝ → ℝ}
    (ht : t ∈ gerverStageIntervals i) (hβ : HasDerivAt β β' t)
    (hαβ : ∀ s ∈ gerverStageIntervals i, paperGerverVelocityComponents s = (α s, β s))
    (hc : α t - β' = c) :
    HasDerivWithinAt (fun s ↦ paperGerverContacts s 3)
      (c • normalVector (t : Real.Angle)) (gerverStageIntervals i) t := by
  have hx : HasDerivAt paperGerverPath (deriv paperGerverPath t) t :=
    (contDiff_paperGerverPath.differentiable one_ne_zero t).hasDerivAt
  have hd := deriv_paperGerverPath_eq_smul_add_smul (hαβ t ht)
  have hmain : HasDerivAt (fun s ↦ paperGerverPath s - β s • normalVector (s : Real.Angle))
      (c • normalVector (t : Real.Angle)) t := by
    have h := hx.sub (hβ.smul (hasDerivAt_normalVector t))
    rw [hd] at h
    rw [← hc]
    convert h using 1
    module
  refine hmain.hasDerivWithinAt.congr (fun y hy ↦ ?_) ?_
  · change paperGerverPath y - (paperGerverVelocityComponents y).2 •
      normalVector (y : Real.Angle) = _
    rw [hαβ y hy]
  · change paperGerverPath t - (paperGerverVelocityComponents t).2 •
      normalVector (t : Real.Angle) = _
    rw [hαβ t ht]

/-- On each of the last two stages the second contact curve moves strictly backwards along
the tangent direction: its one-sided derivative is a negative multiple of `v_t`.  On the
fourth stage the tangential speed is `d₁ - 1 - t/2`, negative because `t ≥ π/2 - θ > 4/5` and
`d₁ ≤ 33/25`; on the fifth it is the exact constant `-1/2`. -/
theorem hasDerivWithinAt_paperGerverContacts_one_neg_smul {i : Fin 5} (hi : i = 3 ∨ i = 4)
    {t : ℝ} (ht : t ∈ gerverStageIntervals i) :
    ∃ c : ℝ, c < 0 ∧
      HasDerivWithinAt (fun s ↦ paperGerverContacts s 1)
        (c • tangentVector (t : Real.Angle)) (gerverStageIntervals i) t := by
  rcases hi with rfl | rfl
  · have hbranch : ∀ s ∈ gerverStageIntervals 3, paperGerverVelocityComponents s =
        ((1 / 4 : ℝ) * s * s - GerverSofa.PartB.params.d1 * s -
            GerverSofa.PartB.params.d2 - 1 / 2,
          2 * GerverSofa.PartB.params.d1 - 1 - s) := by
      intro s hs
      rw [paperGerverContactData_properties.2.2.2 3 s hs]
      rfl
    have hα : HasDerivAt (fun s : ℝ ↦ (1 / 4 : ℝ) * s * s -
        GerverSofa.PartB.params.d1 * s - GerverSofa.PartB.params.d2 - 1 / 2)
        (t / 2 - GerverSofa.PartB.params.d1) t := by
      have h := ((((hasDerivAt_id' t).const_mul (1 / 4 : ℝ)).mul (hasDerivAt_id' t)).sub
        ((hasDerivAt_id' t).const_mul GerverSofa.PartB.params.d1)).sub_const
          GerverSofa.PartB.params.d2 |>.sub_const (1 / 2 : ℝ)
      convert h using 1
      ring
    refine ⟨GerverSofa.PartB.params.d1 - 1 - t / 2, ?_,
      hasDerivWithinAt_paperGerverContacts_one ht hα hbranch (by ring)⟩
    rw [gerverStageIntervals_three] at ht
    have hrefl : gerverStageTimes 3 = Real.pi / 2 - gerverStageTimes 2 := rfl
    linarith [gerverDirectBox_d1_upper_bound GerverSofa.PartB.params_mem,
      gerverStageTimes_two_le_seven_div_ten, ht.1, Real.pi_gt_three]
  · have hbranch : ∀ s ∈ gerverStageIntervals 4, paperGerverVelocityComponents s =
        (1 - 2 * GerverSofa.PartB.params.e1 * Real.sin s +
            2 * GerverSofa.PartB.params.e2 * Real.cos s,
          2 * GerverSofa.PartB.params.e1 * Real.cos s +
            2 * GerverSofa.PartB.params.e2 * Real.sin s - 1 / 2) := by
      intro s hs
      rw [paperGerverContactData_properties.2.2.2 4 s hs]
      rfl
    have hα : HasDerivAt (fun s : ℝ ↦ 1 - 2 * GerverSofa.PartB.params.e1 * Real.sin s +
        2 * GerverSofa.PartB.params.e2 * Real.cos s)
        (-(2 * GerverSofa.PartB.params.e1 * Real.cos t) -
          2 * GerverSofa.PartB.params.e2 * Real.sin t) t := by
      have h := ((hasDerivAt_const t (1 : ℝ)).sub
        ((Real.hasDerivAt_sin t).const_mul (2 * GerverSofa.PartB.params.e1))).add
        ((Real.hasDerivAt_cos t).const_mul (2 * GerverSofa.PartB.params.e2))
      convert h using 1
      ring
    exact ⟨-(1 / 2), by norm_num,
      hasDerivWithinAt_paperGerverContacts_one ht hα hbranch (by ring)⟩

/-- On each of the first two stages the fourth contact curve moves strictly forwards along
the normal direction: its one-sided derivative is a positive multiple of `u_t`.  On the first
stage the normal speed is the exact constant `1/2`; on the second it is `1 + b₁ - t/2`,
positive because `t ≤ θ ≤ 7/10` and `b₁ ≥ -53/100`. -/
theorem hasDerivWithinAt_paperGerverContacts_three_pos_smul {i : Fin 5} (hi : i = 0 ∨ i = 1)
    {t : ℝ} (ht : t ∈ gerverStageIntervals i) :
    ∃ c : ℝ, 0 < c ∧
      HasDerivWithinAt (fun s ↦ paperGerverContacts s 3)
        (c • normalVector (t : Real.Angle)) (gerverStageIntervals i) t := by
  rcases hi with rfl | rfl
  · have hbranch : ∀ s ∈ gerverStageIntervals 0, paperGerverVelocityComponents s =
        (-2 * GerverSofa.PartB.params.a1 * Real.sin s +
            2 * GerverSofa.PartB.params.a2 * Real.cos s + 1 / 2,
          2 * GerverSofa.PartB.params.a1 * Real.cos s +
            2 * GerverSofa.PartB.params.a2 * Real.sin s - 1) := by
      intro s hs
      rw [paperGerverContactData_properties.2.2.2 0 s hs]
      rfl
    have hβ : HasDerivAt (fun s : ℝ ↦ 2 * GerverSofa.PartB.params.a1 * Real.cos s +
        2 * GerverSofa.PartB.params.a2 * Real.sin s - 1)
        (-(2 * GerverSofa.PartB.params.a1 * Real.sin t) +
          2 * GerverSofa.PartB.params.a2 * Real.cos t) t := by
      have h := (((Real.hasDerivAt_cos t).const_mul (2 * GerverSofa.PartB.params.a1)).add
        ((Real.hasDerivAt_sin t).const_mul (2 * GerverSofa.PartB.params.a2))).sub_const (1 : ℝ)
      convert h using 1
      ring
    exact ⟨1 / 2, by norm_num,
      hasDerivWithinAt_paperGerverContacts_three ht hβ hbranch (by ring)⟩
  · have hbranch : ∀ s ∈ gerverStageIntervals 1, paperGerverVelocityComponents s =
        (1 + 2 * GerverSofa.PartB.params.b1 - s,
          -(1 / 4 : ℝ) * s * s + GerverSofa.PartB.params.b1 * s +
            GerverSofa.PartB.params.b2 + 1 / 2) := by
      intro s hs
      rw [paperGerverContactData_properties.2.2.2 1 s hs]
      rfl
    have hβ : HasDerivAt (fun s : ℝ ↦ -(1 / 4 : ℝ) * s * s +
        GerverSofa.PartB.params.b1 * s + GerverSofa.PartB.params.b2 + 1 / 2)
        (-(t / 2) + GerverSofa.PartB.params.b1) t := by
      have h := ((((hasDerivAt_id' t).const_mul (-(1 / 4) : ℝ)).mul (hasDerivAt_id' t)).add
        ((hasDerivAt_id' t).const_mul GerverSofa.PartB.params.b1)).add_const
          GerverSofa.PartB.params.b2 |>.add_const (1 / 2 : ℝ)
      convert h using 1
      ring
    refine ⟨1 + GerverSofa.PartB.params.b1 - t / 2, ?_,
      hasDerivWithinAt_paperGerverContacts_three ht hβ hbranch (by ring)⟩
    rw [gerverStageIntervals_one] at ht
    linarith [gerverDirectBox_b1_lower_bound GerverSofa.PartB.params_mem,
      gerverStageTimes_two_le_seven_div_ten, ht.2]

/-! ### Frame coordinates of the direct path -/

/-- The derivative of the direct Gerver path in the moving frame. -/
theorem hasDerivAt_paperGerverPath_frame (t : ℝ) :
    HasDerivAt paperGerverPath
      ((paperGerverVelocityComponents t).1 • normalVector (t : Real.Angle) +
        (paperGerverVelocityComponents t).2 • tangentVector (t : Real.Angle)) t := by
  have h := (contDiff_paperGerverPath.differentiable one_ne_zero t).hasDerivAt
  rwa [deriv_paperGerverPath_eq_smul_add_smul rfl] at h

/-- The angular derivative of the normal frame coordinate of the Gerver path is the tangent
coordinate of the second contact curve: with `B = x + α v` the frame derivative `u' = v`
contributes `x ⋅ v` and the normal component of `x'` contributes `α`. -/
theorem hasDerivAt_inner_paperGerverPath_normalVector (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (paperGerverPath s) (normalVector (s : Real.Angle)))
      (inner ℝ (paperGerverContacts t 1) (tangentVector (t : Real.Angle))) t := by
  have h := (hasDerivAt_paperGerverPath_frame t).inner ℝ (hasDerivAt_normalVector t)
  convert h using 1
  change inner ℝ (paperGerverPath t + (paperGerverVelocityComponents t).1 •
    tangentVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = _
  rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_left, inner_tangentVector_self, inner_normalVector_self,
    inner_tangentVector_normalVector_real, sub_self, Real.sin_zero]
  ring

/-- The angular derivative of the tangent frame coordinate of the Gerver path is minus the
normal coordinate of the fourth contact curve: with `D = x - β u` the frame derivative
`v' = -u` contributes `-x ⋅ u` and the tangent component of `x'` contributes `β`. -/
theorem hasDerivAt_inner_paperGerverPath_tangentVector (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (paperGerverPath s) (tangentVector (s : Real.Angle)))
      (-inner ℝ (paperGerverContacts t 3) (normalVector (t : Real.Angle))) t := by
  have h := (hasDerivAt_paperGerverPath_frame t).inner ℝ (hasDerivAt_tangentVector t)
  convert h using 1
  change -inner ℝ (paperGerverPath t - (paperGerverVelocityComponents t).2 •
    normalVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = _
  rw [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_left, inner_neg_right, inner_normalVector_self, inner_tangentVector_self,
    inner_normalVector_tangentVector]
  ring

/-! ### Stagewise monotonicity of the inner contact curves against a fixed direction -/

/-- Against the tangent direction at a later angle `c`, the fourth Gerver contact curve is
strictly antitone on each of its first two stages: its stage speed is a positive multiple of
`u_s`, whose `v_c` coordinate is `sin (s - c) < 0`. -/
theorem strictAntiOn_inner_paperGerverContacts_three {i : Fin 5} (hi : i = 0 ∨ i = 1) {c : ℝ}
    (hlt : ∀ s ∈ gerverStageIntervals i, s < c)
    (hwide : ∀ s ∈ gerverStageIntervals i, c - Real.pi < s) :
    StrictAntiOn (fun s ↦ inner ℝ (paperGerverContacts s 3) (tangentVector (c : Real.Angle)))
      (gerverStageIntervals i) := by
  rw [show gerverStageIntervals i =
    Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ) from rfl] at hlt hwide ⊢
  have hspeed : ∀ s ∈ interior (Set.Icc (gerverStageTimes i.castSucc)
      (gerverStageTimes i.succ)), ∃ cs : ℝ, 0 < cs ∧
      derivWithin (fun r ↦ paperGerverContacts r 3)
          (interior (Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ))) s =
        cs • normalVector (s : Real.Angle) ∧
      HasDerivWithinAt (fun r ↦ paperGerverContacts r 3) (cs • normalVector (s : Real.Angle))
        (interior (Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ))) s := by
    intro s hs
    obtain ⟨cs, hcs, hder⟩ :=
      hasDerivWithinAt_paperGerverContacts_three_pos_smul hi (interior_subset hs)
    exact ⟨cs, hcs, (hder.mono interior_subset).derivWithin
      (isOpen_interior.uniqueDiffWithinAt hs), hder.mono interior_subset⟩
  refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
    ((continuous_paperGerverContact 3).continuousOn.inner continuousOn_const)
    (f' := fun s ↦ inner ℝ (derivWithin (fun r ↦ paperGerverContacts r 3)
      (interior (Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ))) s)
      (tangentVector (c : Real.Angle))) ?_ ?_
  · intro s hs
    obtain ⟨cs, -, hu, hder⟩ := hspeed s hs
    rw [hu]
    simpa using
      hder.inner ℝ (hasDerivWithinAt_const s _ (tangentVector (c : Real.Angle)))
  · intro s hs
    obtain ⟨cs, hcs, hu, -⟩ := hspeed s hs
    rw [hu, real_inner_smul_left,
      real_inner_comm (tangentVector (c : Real.Angle)) (normalVector (s : Real.Angle)),
      inner_tangentVector_normalVector_real]
    exact mul_neg_of_pos_of_neg hcs (Real.sin_neg_of_neg_of_neg_pi_lt
      (by linarith only [hlt s (interior_subset hs)])
      (by linarith only [hwide s (interior_subset hs)]))

/-- Against the normal direction at an earlier angle `c`, the second Gerver contact curve is
strictly monotone on each of its last two stages: its stage speed is a negative multiple of
`v_s`, whose `u_c` coordinate is `sin (c - s) < 0`. -/
theorem strictMonoOn_inner_paperGerverContacts_one {i : Fin 5} (hi : i = 3 ∨ i = 4) {c : ℝ}
    (hlt : ∀ s ∈ gerverStageIntervals i, c < s)
    (hwide : ∀ s ∈ gerverStageIntervals i, s < c + Real.pi) :
    StrictMonoOn (fun s ↦ inner ℝ (paperGerverContacts s 1) (normalVector (c : Real.Angle)))
      (gerverStageIntervals i) := by
  rw [show gerverStageIntervals i =
    Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ) from rfl] at hlt hwide ⊢
  have hspeed : ∀ s ∈ interior (Set.Icc (gerverStageTimes i.castSucc)
      (gerverStageTimes i.succ)), ∃ cs : ℝ, cs < 0 ∧
      derivWithin (fun r ↦ paperGerverContacts r 1)
          (interior (Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ))) s =
        cs • tangentVector (s : Real.Angle) ∧
      HasDerivWithinAt (fun r ↦ paperGerverContacts r 1) (cs • tangentVector (s : Real.Angle))
        (interior (Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ))) s := by
    intro s hs
    obtain ⟨cs, hcs, hder⟩ :=
      hasDerivWithinAt_paperGerverContacts_one_neg_smul hi (interior_subset hs)
    exact ⟨cs, hcs, (hder.mono interior_subset).derivWithin
      (isOpen_interior.uniqueDiffWithinAt hs), hder.mono interior_subset⟩
  refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
    ((continuous_paperGerverContact 1).continuousOn.inner continuousOn_const)
    (f' := fun s ↦ inner ℝ (derivWithin (fun r ↦ paperGerverContacts r 1)
      (interior (Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ))) s)
      (normalVector (c : Real.Angle))) ?_ ?_
  · intro s hs
    obtain ⟨cs, -, hu, hder⟩ := hspeed s hs
    rw [hu]
    simpa using
      hder.inner ℝ (hasDerivWithinAt_const s _ (normalVector (c : Real.Angle)))
  · intro s hs
    obtain ⟨cs, hcs, hu, -⟩ := hspeed s hs
    rw [hu, real_inner_smul_left, inner_tangentVector_normalVector_real]
    exact mul_pos_of_neg_of_neg hcs (Real.sin_neg_of_neg_of_neg_pi_lt
      (by linarith only [hlt s (interior_subset hs)])
      (by linarith only [hwide s (interior_subset hs)]))

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Stage endpoints, grid angles and branch selection

The certificate subdivides each of the five analytic stages of Gerver's sofa into
`NN = 64` equal parts.  This module carries the real-valued mirror of that grid:
`gerverStageTime` re-indexes the six stage endpoints by a natural number,
`gerverGridTime m` is the `m`-th grid angle, `gerverContactPoint` is the dictionary of the
four contact curves and the ambient path, and `GerverAreaCert.stageOf m` is the analytic
branch that the piecewise definitions select at the `m`-th angle.  The soundness statements
`endZ_sound` and `ttZ_sound` say that the integer data of the certificate encloses these
real quantities; the remaining lemmas are the order facts the evaluator needs.
-/

public section

noncomputable section

namespace MovingSofa

open GerverAreaCert

/-- The six stage endpoints indexed by a natural number, constant past `5`. -/
@[expose]
def gerverStageTime (s : ℕ) : ℝ := gerverStageTimes ⟨min 5 s, by omega⟩

/-- The real grid angle at index `m`, mirroring `GerverAreaCert.ttZ`. -/
@[expose]
def gerverGridTime (m : ℕ) : ℝ :=
  (((NN - m % NN : ℕ) : ℝ) * gerverStageTime (m / NN) +
    ((m % NN : ℕ) : ℝ) * gerverStageTime (m / NN + 1)) / (NN : ℝ)

/-- The curve selected by a certificate `kind`: `0` the path, `1` `A`, `2` `B`, `3` `C`,
`4` `D`. -/
@[expose]
def gerverContactPoint : ℕ → ℝ → Point
  | 0 => paperGerverPath
  | 1 => fun t ↦ paperGerverContacts t 0
  | 2 => fun t ↦ paperGerverContacts t 1
  | 3 => fun t ↦ paperGerverContacts t 2
  | _ => fun t ↦ paperGerverContacts t 3

/-- The rotation interval starts at the first stage endpoint `0`. -/
theorem gerverStageTime_zero : gerverStageTime 0 = 0 := gerverStageTimes_zero

/-- The first stage ends at `φ`. -/
theorem gerverStageTime_one : gerverStageTime 1 = GerverSofa.PartB.params.phi :=
  gerverStageTimes_one

/-- The second stage ends at `θ`. -/
theorem gerverStageTime_two : gerverStageTime 2 = GerverSofa.PartB.params.theta :=
  gerverStageTimes_two

/-- The third stage ends at `η = π / 2 - θ`. -/
theorem gerverStageTime_three : gerverStageTime 3 = GerverSofa.PartC.eta :=
  gerverStageTimes_three

/-- The fourth stage ends at `τ = π / 2 - φ`. -/
theorem gerverStageTime_four : gerverStageTime 4 = GerverSofa.PartC.tau :=
  gerverStageTimes_four

/-- The fifth stage ends at `π / 2`. -/
theorem gerverStageTime_five : gerverStageTime 5 = Real.pi / 2 := gerverStageTimes_five

/-! ### Order properties of the stage endpoints and the grid -/

/-- The five stage endpoints are strictly increasing. -/
theorem gerverStageTime_lt_succ (s : ℕ) (hs : s < 5) :
    gerverStageTime s < gerverStageTime (s + 1) := by
  refine gerverStageTimes_strictMono ?_
  simp only [Fin.mk_lt_mk]
  omega

/-- Past index `5` the `ℕ`-indexed stage endpoint is constantly `π / 2`. -/
private theorem gerverStageTime_of_five_le {s : ℕ} (hs : 5 ≤ s) :
    gerverStageTime s = Real.pi / 2 := by
  simp only [gerverStageTime, min_eq_left hs]
  exact gerverStageTimes_five

/-- The stage-endpoint enclosure at every index, including those past `5`. -/
private theorem endZ_sound_all (s : ℕ) : SI.Contains (endZ s) (gerverStageTime s) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hphi, htheta⟩ :=
    contains_params
  rcases s with _ | _ | _ | _ | _ | _ | n
  · rw [gerverStageTime_zero]
    exact SI.contains_zero
  · rw [gerverStageTime_one]
    exact hphi
  · rw [gerverStageTime_two]
    exact htheta
  · rw [show gerverStageTime 3 = Real.pi / 2 - GerverSofa.PartB.params.theta from
      gerverStageTime_three]
    exact SI.contains_sub contains_piHalfZ htheta
  · rw [show gerverStageTime 4 = Real.pi / 2 - GerverSofa.PartB.params.phi from
      gerverStageTime_four]
    exact SI.contains_sub contains_piHalfZ hphi
  · rw [gerverStageTime_five]
    exact contains_piHalfZ
  · rw [gerverStageTime_of_five_le (s := n + 6) (by omega)]
    exact contains_piHalfZ

/-- The integer stage endpoints enclose the real ones. -/
theorem endZ_sound (s : ℕ) (hs : s ≤ 5) : SI.Contains (endZ s) (gerverStageTime s) := by
  interval_cases s <;> exact endZ_sound_all _

/-- The integer grid angles enclose the real ones. -/
theorem ttZ_sound (m : ℕ) (hm : m ≤ 5 * NN) : SI.Contains (ttZ m) (gerverGridTime m) := by
  have hNN : (0 : ℤ) < (NN : ℤ) := by norm_num [NN]
  have hdiv : m / NN ≤ 5 := by
    rw [show NN = 64 from rfl] at hm ⊢
    omega
  have key : SI.Contains
      (SI.add (SI.imul ((NN - m % NN : ℕ) : ℤ) (endZ (m / NN)))
        (SI.imul ((m % NN : ℕ) : ℤ) (endZ (m / NN + 1))))
      (((NN - m % NN : ℕ) : ℝ) * gerverStageTime (m / NN) +
        ((m % NN : ℕ) : ℝ) * gerverStageTime (m / NN + 1)) := by
    refine SI.contains_add ?_ ?_
    · have h := SI.contains_imul ((NN - m % NN : ℕ) : ℤ) (endZ_sound (m / NN) hdiv)
      rwa [Int.cast_natCast] at h
    · have h := SI.contains_imul ((m % NN : ℕ) : ℤ) (endZ_sound_all (m / NN + 1))
      rwa [Int.cast_natCast] at h
  have hcast : (((NN : ℤ)) : ℝ) = (NN : ℝ) := by push_cast; ring
  rw [gerverGridTime, ← hcast]
  exact SI.contains_divn hNN key

/-- The grid step is uniform across stage joins. -/
theorem gerverGridTime_succ_sub (m : ℕ) :
    gerverGridTime (m + 1) - gerverGridTime m =
      (gerverStageTime (m / NN + 1) - gerverStageTime (m / NN)) / (NN : ℝ) := by
  have hNNR : (0 : ℝ) < (NN : ℝ) := by norm_num [NN]
  have hr : m % NN < NN := Nat.mod_lt _ (by norm_num [NN])
  have hsplit : ((m + 1) % NN = m % NN + 1 ∧ (m + 1) / NN = m / NN) ∨
      (m % NN + 1 = NN ∧ (m + 1) % NN = 0 ∧ (m + 1) / NN = m / NN + 1) := by
    rw [show NN = 64 from rfl]
    omega
  rcases hsplit with ⟨hmod, hdiv⟩ | ⟨hfull, hmod, hdiv⟩
  · rw [gerverGridTime, gerverGridTime, hmod, hdiv,
      Nat.cast_sub (by omega : m % NN + 1 ≤ NN), Nat.cast_sub hr.le]
    push_cast
    field_simp
    ring
  · rw [gerverGridTime, gerverGridTime, hmod, hdiv, Nat.cast_sub hr.le]
    have hrR : ((m % NN : ℕ) : ℝ) = (NN : ℝ) - 1 := by
      have : ((m % NN + 1 : ℕ) : ℝ) = ((NN : ℕ) : ℝ) := by rw [hfull]
      push_cast at this
      linarith
    rw [hrR]
    simp only [Nat.sub_zero]
    push_cast
    field_simp
    ring

/-- The grid angles are strictly increasing. -/
theorem gerverGridTime_lt_succ (m : ℕ) (hm : m < 5 * NN) :
    gerverGridTime m < gerverGridTime (m + 1) := by
  have hNNR : (0 : ℝ) < (NN : ℝ) := by norm_num [NN]
  have hlt : m / NN < 5 := (Nat.div_lt_iff_lt_mul (by norm_num [NN])).mpr hm
  have hstep := gerverGridTime_succ_sub m
  have hstage := gerverStageTime_lt_succ (m / NN) hlt
  have hpos : 0 < (gerverStageTime (m / NN + 1) - gerverStageTime (m / NN)) / (NN : ℝ) :=
    div_pos (by linarith) hNNR
  linarith

/-- Strict monotonicity of the grid angles below the top index, from `gerverGridTime_lt_succ`. -/
theorem gerverGridTime_lt_of_lt {m n : ℕ} (hmn : m < n) (hn : n ≤ 5 * NN) :
    gerverGridTime m < gerverGridTime n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hmn with h | h
    · exact (ih h (by omega)).trans (gerverGridTime_lt_succ n (by omega))
    · subst h
      exact gerverGridTime_lt_succ m (by omega)

/-- Weak monotonicity of the grid angles below the top index, from `gerverGridTime_lt_succ`. -/
theorem gerverGridTime_le_of_le {m n : ℕ} (hmn : m ≤ n) (hn : n ≤ 5 * NN) :
    gerverGridTime m ≤ gerverGridTime n := by
  rcases eq_or_lt_of_le hmn with rfl | h
  · exact le_rfl
  · exact (gerverGridTime_lt_of_lt h hn).le

/-- The grid angle at a stage boundary is the stage endpoint itself. -/
theorem gerverGridTime_mul_NN (s : ℕ) : gerverGridTime (s * NN) = gerverStageTime s := by
  have hNN : 0 < NN := by norm_num [NN]
  have hne : (NN : ℝ) ≠ 0 := by norm_num [NN]
  rw [gerverGridTime, Nat.mul_mod_left, Nat.mul_div_cancel _ hNN]
  simp only [Nat.sub_zero, Nat.cast_zero, zero_mul, add_zero]
  exact mul_div_cancel_left₀ _ hne

/-- The grid starts at `0`. -/
theorem gerverGridTime_zero : gerverGridTime 0 = 0 := by
  have h := gerverGridTime_mul_NN 0
  rw [zero_mul] at h
  rw [h, gerverStageTime_zero]

/-- The grid ends at `π / 2`. -/
theorem gerverGridTime_top : gerverGridTime (5 * NN) = Real.pi / 2 := by
  rw [gerverGridTime_mul_NN 5, gerverStageTime_five]

/-- Every grid angle lies in the rotation interval. -/
theorem gerverGridTime_mem_Icc (m : ℕ) (hm : m ≤ 5 * NN) :
    gerverGridTime m ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
  refine ⟨?_, ?_⟩
  · rw [← gerverGridTime_zero]
    exact gerverGridTime_le_of_le (Nat.zero_le m) hm
  · rw [← gerverGridTime_top]
    exact gerverGridTime_le_of_le hm le_rfl

/-- The branch index is one of the five stages. -/
theorem stageOf_mem (m : ℕ) (hm : m ≤ 5 * NN) : 1 ≤ stageOf m ∧ stageOf m ≤ 5 := by
  have hNN : 0 < NN := by norm_num [NN]
  have hd : m / NN ≤ 5 := Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact hm)
  rw [stageOf]
  split_ifs with h
  · exact ⟨le_max_left _ _, max_le (by omega) hd⟩
  · have hmlt : m < 5 * NN := by
      rcases lt_or_eq_of_le hm with h' | h'
      · exact h'
      · subst h'; exact absurd (Nat.mul_mod_left 5 NN) h
    have hd4 : m / NN < 5 := (Nat.div_lt_iff_lt_mul hNN).mpr hmlt
    exact ⟨Nat.le_add_left 1 _, hd4⟩

/-- The grid angle does not exceed the right endpoint of its branch. -/
theorem gerverGridTime_le_stageTime (m : ℕ) (hm : m ≤ 5 * NN) :
    gerverGridTime m ≤ gerverStageTime (stageOf m) := by
  have hNN : 0 < NN := by norm_num [NN]
  rw [stageOf]
  split_ifs with h
  · have hmm : m / NN * NN = m := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)
    have key : gerverGridTime m = gerverStageTime (m / NN) := by
      have h' := gerverGridTime_mul_NN (m / NN)
      rwa [hmm] at h'
    rcases Nat.eq_zero_or_pos (m / NN) with h0 | h0
    · have hm0 : m = 0 := by rw [← hmm, h0, zero_mul]
      rw [h0, show max 1 0 = 1 from rfl, hm0, gerverGridTime_zero]
      have h01 := gerverStageTime_lt_succ 0 (by norm_num)
      rw [gerverStageTime_zero] at h01
      exact h01.le
    · rw [max_eq_right h0, key]
  · have hmlt : m < 5 * NN := by
      rcases lt_or_eq_of_le hm with h' | h'
      · exact h'
      · subst h'; exact absurd (Nat.mul_mod_left 5 NN) h
    have hd4 : m / NN < 5 := (Nat.div_lt_iff_lt_mul hNN).mpr hmlt
    have hlt : m < (m / NN + 1) * NN := (Nat.div_lt_iff_lt_mul hNN).mp (Nat.lt_succ_self _)
    have hub : (m / NN + 1) * NN ≤ 5 * NN := Nat.mul_le_mul_right NN hd4
    calc gerverGridTime m ≤ gerverGridTime ((m / NN + 1) * NN) :=
          gerverGridTime_le_of_le hlt.le hub
      _ = gerverStageTime (m / NN + 1) := gerverGridTime_mul_NN _

/-- The grid angle strictly exceeds the left endpoint of its branch, except on the
first branch. -/
theorem stageTime_lt_gerverGridTime (m : ℕ) (hm : m ≤ 5 * NN) (h2 : 2 ≤ stageOf m) :
    gerverStageTime (stageOf m - 1) < gerverGridTime m := by
  have hNN : 0 < NN := by norm_num [NN]
  have hd5 : m / NN ≤ 5 := Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact hm)
  rw [stageOf] at h2 ⊢
  split_ifs at h2 ⊢ with h
  · have hd : 2 ≤ m / NN := by
      rcases le_max_iff.mp h2 with h' | h'
      · exact absurd h' (by norm_num)
      · exact h'
    have hpos : 0 < m / NN := lt_of_lt_of_le (by norm_num) hd
    have hmm : m / NN * NN = m := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)
    have key : gerverGridTime m = gerverStageTime (m / NN) := by
      have h' := gerverGridTime_mul_NN (m / NN)
      rwa [hmm] at h'
    rw [max_eq_right (Nat.le_of_succ_le hd), key]
    have h4 : m / NN - 1 < 5 := lt_of_le_of_lt (Nat.sub_le_sub_right hd5 1) (by norm_num)
    have hlt := gerverStageTime_lt_succ (m / NN - 1) h4
    rwa [Nat.sub_add_cancel hpos] at hlt
  · rw [Nat.add_sub_cancel]
    have hle : m / NN * NN ≤ m := Nat.div_mul_le_self m NN
    have hne : m / NN * NN ≠ m := by
      intro he
      exact h (by rw [← he]; exact Nat.mul_mod_left _ _)
    have key : gerverGridTime (m / NN * NN) = gerverStageTime (m / NN) := gerverGridTime_mul_NN _
    rw [← key]
    exact gerverGridTime_lt_of_lt (lt_of_le_of_ne hle hne) hm

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Properties of the Gerver niche roof

The main results of this file describe the upper boundary of the paper's literal Gerver
niche: the three graph pieces join up (`gerver_niche_piece_endpoints`), each piece stays
inside the outer cap (`gerver_niche_roof_membership`), the roof is a strictly monotone
positive graph (`gerver_niche_roof_strictMono`, `gerver_niche_roof_positive`), and the
niche is exactly the strict vertical region under that roof (`gerver_niche_vertical_fills`).
The three pieces are identified branch by branch in `gerverNicheRoof_of_le_two`,
`gerverNicheRoof_mid` and `gerverNicheRoof_of_ge_three`, each valid on the closed stage.

Alongside them sits the elementary API of the reverse-time reparametrization
(`continuous_gerverRoofReverseTime`, `gerverRoofReverseTime_two`,
`gerverRoofReverseTime_three`, `gerverRoofReverseTime_mem_Icc`) and the continuity of the
roof, in both its real-parameter and its restricted form (`continuous_gerverRoofCurve`,
`continuous_gerverNicheRoof`).

Every one of them is the certified Part C niche geometry read through the coordinate
dictionary `GerverSofa.PartF.Coordinates.toPlane`.  The dictionary itself is supplied by
the public readers of the lower modules — `paperGerverContacts_one_eq_toPlane` and
`paperGerverContacts_three_eq_toPlane` for the contact curves, `gerverStageTimes_zero`
through `gerverStageTimes_five` for the stage times, and `mem_gerverLiteralNiche_iff`,
`toPlane_mem_gerverOuterCap` for the two literal sets.  What remains here, and is kept
private, is the roof-specific part of the dictionary: the reverse-time reparametrization
and the identification of `gerverNicheRoof` with the certified upper arc.
-/

public section

noncomputable section

namespace MovingSofa

section Roof

open GerverSofa.PartF.Coordinates
open GerverSofa.PartC (params eta tau)

/-- The roof reverse-time reparametrization is the certified affine reversal of the core
stage, which sends `params.theta` to `tau` and `eta` to `params.phi`. -/
private theorem gerverRoofReverseTime_eq (s : ℝ) :
    gerverRoofReverseTime s = GerverSofa.PartC.Stage4.coreReverseTime s := by
  rw [gerverRoofReverseTime, gerverStageTimes_four, gerverStageTimes_one,
    gerverStageTimes_three, gerverStageTimes_two]
  rfl

/-- The Gerver roof is the certified upper niche arc, read in plane coordinates.  The three
branches of `gerverNicheRoof` match the three branches of `nicheTopArc` piece for piece,
with the same cut points `params.theta` and `eta`. -/
private theorem gerverNicheRoof_eq_toPlane (s : Set.Icc (0 : ℝ) (Real.pi / 2)) :
    gerverNicheRoof s = toPlane (GerverSofa.PartC.Stage4.nicheTopArc s.val) := by
  have hsI : (s : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := s.2
  simp only [gerverNicheRoof, GerverSofa.PartC.Stage4.nicheTopArc, gerverStageTimes_two,
    gerverStageTimes_three, gerverRoofReverseTime_eq]
  split_ifs with h1 h2
  · exact paperGerverContacts_three_eq_toPlane hsI
  · rfl
  · exact paperGerverContacts_one_eq_toPlane hsI

end Roof

/-- The three graph pieces of the niche roof join up: the second contact curve at `eta`
meets the ambient path at `params.phi`, the fourth contact curve at `params.theta` meets
the ambient path at `tau`, and the two outer ends touch the wall. -/
theorem gerver_niche_piece_endpoints :
    paperGerverContacts (gerverStageTimes 3) 1 = paperGerverPath (gerverStageTimes 1) ∧
    paperGerverContacts (gerverStageTimes 2) 3 = paperGerverPath (gerverStageTimes 4) ∧
    paperGerverContacts (Real.pi / 2) 1 1 = 0 ∧ paperGerverContacts 0 3 1 = 0 := by
  open GerverSofa.PartF.Coordinates GerverSofa.PartC GerverSofa.PartC.Stage4 in
  obtain ⟨hB, hD, hBT, hD0⟩ := GerverSofa.PartC.Stage4.niche_piece_endpoints
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hTeq : GerverSofa.PartC.T = Real.pi / 2 := rfl
  have hchain : 0 < params.theta ∧ params.theta < eta ∧ eta < tau ∧ tau < Real.pi / 2 :=
    ⟨GerverSofa.PartC.Stage4.theta_pos, GerverSofa.PartC.Stage4.theta_lt_eta,
      GerverSofa.PartC.Stage4.eta_lt_tau, hTeq ▸ GerverSofa.PartC.Stage4.tau_lt_T⟩
  obtain ⟨hθ0, hθη, hητ, hτT⟩ := hchain
  have hth : params.theta ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hθ0.le, by linarith⟩
  have heta : eta ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨by linarith, by linarith⟩
  have hTm : (Real.pi / 2) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hpi.le, le_rfl⟩
  have h0m : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_rfl, hpi.le⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [gerverStageTimes_three, gerverStageTimes_one,
      paperGerverContacts_one_eq_toPlane heta, paperGerverPath_eq_toPlane]
    exact congrArg toPlane hB
  · rw [gerverStageTimes_two, gerverStageTimes_four,
      paperGerverContacts_three_eq_toPlane hth, paperGerverPath_eq_toPlane]
    exact congrArg toPlane hD
  · rw [paperGerverContacts_one_eq_toPlane hTm]
    exact hBT
  · rw [paperGerverContacts_three_eq_toPlane h0m]
    exact hD0

/-! ## The reverse-time reparametrization, and continuity of the roof -/

/-- The reverse-time reparametrization is affine, hence continuous. -/
theorem continuous_gerverRoofReverseTime : Continuous gerverRoofReverseTime := by
  unfold gerverRoofReverseTime
  fun_prop

/-- The reverse-time map sends the start of the middle roof stage to the late path time. -/
theorem gerverRoofReverseTime_two :
    gerverRoofReverseTime (gerverStageTimes 2) = gerverStageTimes 4 := by
  rw [gerverRoofReverseTime, sub_self, mul_zero, sub_zero]

/-- The reverse-time map sends the end of the middle roof stage to the early path time. -/
theorem gerverRoofReverseTime_three :
    gerverRoofReverseTime (gerverStageTimes 3) = gerverStageTimes 1 := by
  have h23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_strictMono (by decide)
  rw [gerverRoofReverseTime, div_mul_cancel₀ _ (sub_ne_zero.mpr h23.ne')]
  ring

/-- The reverse-time map carries the middle roof interval into the central path interval. -/
theorem gerverRoofReverseTime_mem_Icc {s : ℝ} (h1 : gerverStageTimes 2 ≤ s)
    (h2 : s ≤ gerverStageTimes 3) :
    gerverRoofReverseTime s ∈ Set.Icc (gerverStageTimes 1) (gerverStageTimes 4) := by
  have h12 : gerverStageTimes 1 < gerverStageTimes 2 := gerverStageTimes_strictMono (by decide)
  have h23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_strictMono (by decide)
  have h34 : gerverStageTimes 3 < gerverStageTimes 4 := gerverStageTimes_strictMono (by decide)
  have hd : (0 : ℝ) < gerverStageTimes 3 - gerverStageTimes 2 := by linarith
  have hL : 0 < (gerverStageTimes 4 - gerverStageTimes 1) /
      (gerverStageTimes 3 - gerverStageTimes 2) := div_pos (by linarith) hd
  have hmul := mul_le_mul_of_nonneg_left (show s - gerverStageTimes 2 ≤
    gerverStageTimes 3 - gerverStageTimes 2 by linarith) hL.le
  rw [div_mul_cancel₀ _ hd.ne'] at hmul
  have hnn : 0 ≤ (gerverStageTimes 4 - gerverStageTimes 1) /
      (gerverStageTimes 3 - gerverStageTimes 2) * (s - gerverStageTimes 2) :=
    mul_nonneg hL.le (by linarith)
  rw [gerverRoofReverseTime]
  constructor <;> linarith

/-! ## The three graph pieces of the roof -/

/-- Up to the second stage time the niche roof is the fourth contact curve. -/
theorem gerverNicheRoof_of_le_two {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (h : s ≤ gerverStageTimes 2) : gerverNicheRoof ⟨s, hs⟩ = paperGerverContacts s 3 :=
  ite_eq_left h

/-- On the middle stage the niche roof is the reverse-time ambient path.  The identification
extends to the left endpoint of the stage by the piece-endpoint gluing. -/
theorem gerverNicheRoof_mid {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (h1 : gerverStageTimes 2 ≤ s) (h2 : s ≤ gerverStageTimes 3) :
    gerverNicheRoof ⟨s, hs⟩ = paperGerverPath (gerverRoofReverseTime s) := by
  rcases eq_or_lt_of_le h1 with heq | hlt
  · rw [gerverNicheRoof_of_le_two hs heq.ge, ← heq, gerverRoofReverseTime_two]
    exact gerver_niche_piece_endpoints.2.1
  · rw [gerverNicheRoof, ite_eq_right (not_le.mpr hlt), ite_eq_left h2]

/-- From the third stage time on the niche roof is the second contact curve.  The
identification extends to the left endpoint of the stage by the piece-endpoint gluing. -/
theorem gerverNicheRoof_of_ge_three {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (h : gerverStageTimes 3 ≤ s) : gerverNicheRoof ⟨s, hs⟩ = paperGerverContacts s 1 := by
  have h23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_strictMono (by decide)
  rcases eq_or_lt_of_le h with heq | hlt
  · rw [gerverNicheRoof_mid hs (by linarith) heq.ge, ← heq, gerverRoofReverseTime_three]
    exact gerver_niche_piece_endpoints.1.symm
  · rw [gerverNicheRoof, ite_eq_right (not_le.mpr (by linarith)),
      ite_eq_right (not_le.mpr hlt)]

/-- On the rotation interval the real-parameter roof curve is the niche roof. -/
theorem gerverRoofCurve_eq (s : Set.Icc (0 : ℝ) (Real.pi / 2)) :
    gerverRoofCurve s.val = gerverNicheRoof s := rfl

/-- The roof curve is continuous: its three graph pieces join up at the two cut times, by the
two endpoint identities of `gerver_niche_piece_endpoints`. -/
theorem continuous_gerverRoofCurve : Continuous gerverRoofCurve := by
  have h23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_strictMono (by decide)
  have hinner : Continuous fun s : ℝ ↦
      if s ≤ gerverStageTimes 3 then paperGerverPath (gerverRoofReverseTime s)
      else paperGerverContacts s 1 := by
    refine continuous_if_le continuous_id continuous_const
      ((contDiff_paperGerverPath.continuous.comp continuous_gerverRoofReverseTime).continuousOn)
      ((continuous_paperGerverContact 1).continuousOn) ?_
    intro s hs
    rw [hs, gerverRoofReverseTime_three]
    exact gerver_niche_piece_endpoints.1.symm
  refine continuous_if_le continuous_id continuous_const
    ((continuous_paperGerverContact 3).continuousOn) hinner.continuousOn ?_
  intro s hs
  rw [ite_eq_left (by rw [hs]; exact h23.le), hs, gerverRoofReverseTime_two]
  exact gerver_niche_piece_endpoints.2.1

/-- The niche roof is continuous. -/
theorem continuous_gerverNicheRoof : Continuous gerverNicheRoof :=
  continuous_gerverRoofCurve.comp continuous_subtype_val

/-- The first coordinate of the niche roof is strictly increasing, so the roof really is a
graph over the horizontal axis. -/
theorem gerver_niche_roof_strictMono :
    StrictMono (fun s : Set.Icc (0 : ℝ) (Real.pi / 2) ↦ gerverNicheRoof s 0) := by
  intro a b hab
  have h := GerverSofa.PartC.Stage4.nicheTopArc_fst_strictMono a.2 b.2 hab
  simp only [gerverNicheRoof_eq_toPlane]
  exact h

/-- The niche roof has positive height strictly inside the rotation interval. -/
theorem gerver_niche_roof_positive
    (s : Set.Icc (0 : ℝ) (Real.pi / 2)) (hs : 0 < s.val ∧ s.val < Real.pi / 2) :
    0 < gerverNicheRoof s 1 := by
  rw [gerverNicheRoof_eq_toPlane]
  exact GerverSofa.PartC.Stage4.nicheTopArc_y_pos ⟨hs.1, hs.2⟩

/-- Each of the three graph pieces of the niche roof stays inside the paper outer cap. -/
theorem gerver_niche_roof_membership :
    (∀ t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2),
      paperGerverContacts t 3 ∈ gerverOuterCap) ∧
    (∀ t ∈ Set.Icc (gerverStageTimes 1) (gerverStageTimes 4),
      paperGerverPath t ∈ gerverOuterCap) ∧
    (∀ t ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5),
      paperGerverContacts t 1 ∈ gerverOuterCap) := by
  open GerverSofa.PartF.Coordinates GerverSofa.PartC GerverSofa.PartC.Stage4 in
  obtain ⟨hD, hx, hB⟩ := GerverSofa.PartC.Stage4.certified_roof_mem_K
  have hTeq : GerverSofa.PartC.T = Real.pi / 2 := rfl
  have hθ0 : 0 < params.theta := GerverSofa.PartC.Stage4.theta_pos
  have hθη : params.theta < eta := GerverSofa.PartC.Stage4.theta_lt_eta
  have hητ : eta < tau := GerverSofa.PartC.Stage4.eta_lt_tau
  have hτT : tau < Real.pi / 2 := hTeq ▸ GerverSofa.PartC.Stage4.tau_lt_T
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rw [gerverStageTimes_zero, gerverStageTimes_two] at ht
    have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨ht.1, by linarith [ht.2]⟩
    rw [paperGerverContacts_three_eq_toPlane htI]
    exact toPlane_mem_gerverOuterCap (hD t ht)
  · intro t ht
    rw [gerverStageTimes_one, gerverStageTimes_four] at ht
    exact toPlane_mem_gerverOuterCap (hx t ht)
  · intro t ht
    rw [gerverStageTimes_three, gerverStageTimes_five] at ht
    have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [ht.1], hTeq ▸ ht.2⟩
    rw [paperGerverContacts_one_eq_toPlane htI]
    exact toPlane_mem_gerverOuterCap (hB t ht)

/-- The strict region between the wall and the graph of `f` over the parameter set `I`. -/
@[expose]
def strictVerticalFill (f : ℝ → Point) (I : Set ℝ) : Set Point :=
  {q | ∃ t ∈ I, q 0 = f t 0 ∧ 0 ≤ q 1 ∧ q 1 < f t 1}

section Fills

open GerverSofa.PartF.Coordinates
open GerverSofa.PartC (params eta tau)

/-- A strict vertical fill is the coordinate preimage of the certified vertical fill under
the plane dictionary. -/
private theorem strictVerticalFill_eq_preimage {F : ℝ → Point} {g : ℝ → GerverSofa.Point}
    {I : Set ℝ} (h : ∀ t ∈ I, F t = toPlane (g t)) :
    strictVerticalFill F I = fromPlane ⁻¹' GerverSofa.PartC.Stage4.verticalFill g I := by
  ext q
  constructor
  · rintro ⟨t, ht, h0, h1, h2⟩
    rw [h t ht] at h0 h2
    exact ⟨t, ht, h0, h1, h2⟩
  · rintro ⟨t, ht, h0, h1, h2⟩
    refine ⟨t, ht, ?_, h1, ?_⟩
    · rw [h t ht]; exact h0
    · rw [h t ht]; exact h2

end Fills

/-- The paper literal niche is exactly the union of the three strict vertical fills under
the three graph pieces of the niche roof. -/
theorem gerver_niche_vertical_fills :
    gerverLiteralNiche =
      strictVerticalFill (fun t ↦ paperGerverContacts t 3)
        (Set.Icc (gerverStageTimes 0) (gerverStageTimes 2)) ∪
      strictVerticalFill paperGerverPath
        (Set.Icc (gerverStageTimes 1) (gerverStageTimes 4)) ∪
      strictVerticalFill (fun t ↦ paperGerverContacts t 1)
        (Set.Icc (gerverStageTimes 3) (gerverStageTimes 5)) := by
  open GerverSofa.PartF.Coordinates GerverSofa.PartC GerverSofa.PartC.Stage4 in
  have hTeq : GerverSofa.PartC.T = Real.pi / 2 := rfl
  have hθ0 : 0 < params.theta := GerverSofa.PartC.Stage4.theta_pos
  have hθη : params.theta < eta := GerverSofa.PartC.Stage4.theta_lt_eta
  have hητ : eta < tau := GerverSofa.PartC.Stage4.eta_lt_tau
  have hτT : tau < Real.pi / 2 := hTeq ▸ GerverSofa.PartC.Stage4.tau_lt_T
  have hDeq : ∀ t ∈ Set.Icc (0 : ℝ) params.theta,
      (fun t ↦ paperGerverContacts t 3) t = toPlane (GerverSofa.PartC.D t) := fun t ht =>
    paperGerverContacts_three_eq_toPlane ⟨ht.1, by linarith [ht.2]⟩
  have hpeq : ∀ t ∈ Set.Icc params.phi tau,
      paperGerverPath t = toPlane (GerverSofa.Romik.path params t) := fun _ _ => rfl
  have hBeq : ∀ t ∈ Set.Icc eta GerverSofa.PartC.T,
      (fun t ↦ paperGerverContacts t 1) t = toPlane (GerverSofa.PartC.B t) := fun t ht =>
    paperGerverContacts_one_eq_toPlane ⟨by linarith [ht.1], hTeq ▸ ht.2⟩
  rw [gerverStageTimes_zero, gerverStageTimes_two, gerverStageTimes_one, gerverStageTimes_four,
    gerverStageTimes_three, gerverStageTimes_five, strictVerticalFill_eq_preimage hDeq,
    strictVerticalFill_eq_preimage hpeq, strictVerticalFill_eq_preimage hBeq,
    ← Set.preimage_union, ← Set.preimage_union]
  exact Set.ext fun q =>
    (mem_gerverLiteralNiche_iff q).trans
      (by rw [GerverSofa.PartC.Stage4.niche_eq_certifiedNicheRegion]; rfl)

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Cap.Tail.Arcs`.
* `Cap.Tail.Space`.
* `Cap.CornerMeasure`.
* `Cap.CornerPaths`.
* `Cap.Tail.Canonical`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Tail / Arcs
-/

public section

noncomputable section

namespace MovingSofa

/-- A planar carrier set equipped with ordered start and end points. -/
structure DirectedArcData where
  /-- The set traced by the directed arc. -/
  carrier : Set Point
  /-- The starting point of the arc. -/
  startPoint : Point
  /-- The ending point of the arc. -/
  endPoint : Point

/-- The directed convex boundary arcs used for the right and left tail bodies. -/
@[expose]
def rightLeftTailArcs (B D : ConvexBody Point) : DirectedArcData × DirectedArcData :=
  (⟨convexBoundaryArc B (Real.pi + paperGerverConstants.2.1) (3 * Real.pi / 2),
    (edgeVertices B ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)).1,
    (edgeVertices B ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2⟩,
   ⟨convexBoundaryArc D (3 * Real.pi / 2) (3 * Real.pi / 2 + paperGerverConstants.2.2),
    (edgeVertices D ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1,
    (edgeVertices D ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)).2⟩)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Tail / Space
-/

public section

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace MovingSofa

/-- The real-angle inner-corner path of a cap. -/
@[expose]
def capInnerCorner (K : RightAngleCapSpace) (t : ℝ) : Point :=
  (rotatingHallwayParts (K.1 : Set Point) (t : Real.Angle)).innerCorner

/-- The two surface densities on the upper half-circle, with the top atom excluded. -/
@[expose]
def HasCapDensities (K : RightAngleCapSpace) (r s : ℝ → ℝ≥0) : Prop :=
  Measurable r ∧ Measurable s ∧
    (surfaceAreaMeasure K.1).restrict
        ((fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ico 0 (Real.pi / 2)) =
      Measure.map (fun t : ℝ ↦ (t : Real.Angle))
        ((volume.restrict (Set.Ico 0 (Real.pi / 2))).withDensity (fun t ↦ (r t : ℝ≥0∞))) ∧
    (surfaceAreaMeasure K.1).restrict
        ((fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioc (Real.pi / 2) Real.pi) =
      Measure.map (fun t : ℝ ↦ ((t + Real.pi / 2 : ℝ) : Real.Angle))
        ((volume.restrict (Set.Ioc 0 (Real.pi / 2))).withDensity (fun t ↦ (s t : ℝ≥0∞)))

/-- The density, corner regularity and strict interior signs of the injectivity condition. -/
@[expose]
def SatisfiesInjectivityCondition (K : RightAngleCapSpace) : Prop :=
  (∃ r s : ℝ → ℝ≥0, HasCapDensities K r s ∧
    ∀ r' s', HasCapDensities K r' s' →
      (r =ᵐ[volume.restrict (Set.Icc 0 (Real.pi / 2))] r') ∧
      (s =ᵐ[volume.restrict (Set.Icc 0 (Real.pi / 2))] s')) ∧
    ContDiffOn ℝ 1 (capInnerCorner K) (Set.Icc 0 (Real.pi / 2)) ∧
    ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      inner ℝ (derivWithin (capInnerCorner K) (Set.Icc 0 (Real.pi / 2)) t)
        (normalVector (t : Real.Angle)) < 0 ∧
      0 < inner ℝ (derivWithin (capInnerCorner K) (Set.Icc 0 (Real.pi / 2)) t)
        (tangentVector (t : Real.Angle))

/-- Right-angle caps satisfying injectivity and the cap-area threshold. -/
@[expose]
def SpecialCapSpace :=
  {K : RightAngleCapSpace // SatisfiesInjectivityCondition K ∧
    (11 : ℝ) / 5 ≤ ClassicalResults.area (K.1 : Set Point)}

/-- A special cap and two convex tails satisfying the support constraints. -/
structure CapTailSpace where
  /-- The special cap forming the central component of the triple. -/
  cap : SpecialCapSpace
  /-- The convex body used as the right tail. -/
  rightBody : ConvexBody Point
  /-- The convex body used as the left tail. -/
  leftBody : ConvexBody Point
  right_subset : (rightBody : Set Point) ⊆ (cap.1.1 : Set Point)
  left_subset : (leftBody : Set Point) ⊆ (cap.1.1 : Set Point)
  right_bound : ∀ t ∈ Set.Icc paperGerverConstants.2.1 (Real.pi / 2),
    supportValue cap.1.1 (t : Real.Angle) +
      supportValue rightBody ((Real.pi + t : ℝ) : Real.Angle) ≤ 1
  right_eq : ∀ t ∈ ({paperGerverConstants.2.1, Real.pi / 2} : Set ℝ),
    supportValue cap.1.1 (t : Real.Angle) +
      supportValue rightBody ((Real.pi + t : ℝ) : Real.Angle) = 1
  left_bound : ∀ t ∈ Set.Icc (0 : ℝ) paperGerverConstants.2.2,
    supportValue cap.1.1 ((Real.pi / 2 + t : ℝ) : Real.Angle) +
      supportValue leftBody ((3 * Real.pi / 2 + t : ℝ) : Real.Angle) ≤ 1
  left_eq : ∀ t ∈ ({0, paperGerverConstants.2.2} : Set ℝ),
    supportValue cap.1.1 ((Real.pi / 2 + t : ℝ) : Real.Angle) +
      supportValue leftBody ((3 * Real.pi / 2 + t : ℝ) : Real.Angle) = 1

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Corner Measure
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- The normal and tangent components of the inner-corner path derivative. -/
@[expose]
def capVelocityCoefficients (K : SpecialCapSpace) (t : ℝ) : ℝ × ℝ :=
  (inner ℝ (derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t)
      (normalVector (t : Real.Angle)),
    inner ℝ (derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t)
      (tangentVector (t : Real.Angle)))

/-- The density formed by joining the two signed corner-velocity components over `[0, π]`. -/
@[expose]
def capCornerDensity (K : SpecialCapSpace) (s : ℝ) : ℝ :=
  if 0 < s ∧ s ≤ Real.pi / 2 then (capVelocityCoefficients K s).2
  else if Real.pi / 2 < s ∧ s ≤ Real.pi then
    -(capVelocityCoefficients K (s - Real.pi / 2)).1
  else 0

/-- The measure on the real angle interval defined by the nonnegative corner density. -/
@[expose]
def capCornerMeasure (K : SpecialCapSpace) : Measure ℝ :=
  (volume.restrict (Set.Icc 0 Real.pi)).withDensity
    (fun s ↦ ENNReal.ofReal (capCornerDensity K s))

/-- Push the corner-density measure to angles modulo a full turn. -/
@[expose]
def capCornerAngleMeasure (K : SpecialCapSpace) : Measure Real.Angle :=
  Measure.map (fun s : ℝ ↦ (s : Real.Angle)) (capCornerMeasure K)

/-- Bundle the corner density and its real and angular measures. -/
def capCornerMeasureData (K : SpecialCapSpace) :
    (ℝ → ℝ) × Measure ℝ × Measure Real.Angle :=
  (capCornerDensity K, capCornerMeasure K, capCornerAngleMeasure K)

/-- The corner measure of a special cap reads its density on the angular image of every
measurable subset of `[0, π]`. -/
theorem capCornerAngleMeasure_angleImage_eq_setLIntegral (K : SpecialCapSpace) {T : Set ℝ}
    (hT : MeasurableSet T) (hT' : T ⊆ Set.Icc 0 Real.pi) :
    capCornerAngleMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' T) =
      ∫⁻ s in T, ENNReal.ofReal (capCornerDensity K s) := by
  have hturn : Real.pi ≤ -1 + 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hsub : Set.Icc (0 : ℝ) Real.pi ⊆ Set.Ioc (-1 : ℝ) Real.pi :=
    fun x hx ↦ ⟨by linarith [hx.1], hx.2⟩
  change Measure.map (fun s : ℝ ↦ (s : Real.Angle))
      ((volume.restrict (Set.Icc 0 Real.pi)).withDensity
        (fun s ↦ ENNReal.ofReal (capCornerDensity K s)))
      ((fun s : ℝ ↦ (s : Real.Angle)) '' T) = _
  exact Real.Angle.map_coe_withDensity_image_eq_setLIntegral hturn hsub hT hT'

/-! ### Regularity and signs of the corner density

The injectivity condition makes the inner corner continuously differentiable on the closed
quarter turn, so both frame coefficients of its velocity are continuous there; the strict interior
signs then extend to the two endpoints by continuity.  The corner density is the sum of the two
branches extended by zero, whence its measurability and its bound. -/

/-- The inner-corner velocity of a special cap is continuous on the cap domain. -/
theorem continuousOn_derivWithin_capInnerCorner (K : SpecialCapSpace) :
    ContinuousOn (derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)))
      (Set.Icc 0 (Real.pi / 2)) :=
  K.property.1.2.1.continuousOn_derivWithin
    (uniqueDiffOn_Icc (by positivity : (0 : ℝ) < Real.pi / 2)) le_rfl

/-- Both frame components of the inner-corner velocity are continuous on the cap domain. -/
theorem continuousOn_capVelocityCoefficients (K : SpecialCapSpace) :
    ContinuousOn (fun s ↦ (capVelocityCoefficients K s).1) (Set.Icc 0 (Real.pi / 2)) ∧
      ContinuousOn (fun s ↦ (capVelocityCoefficients K s).2) (Set.Icc 0 (Real.pi / 2)) :=
  ⟨(continuousOn_derivWithin_capInnerCorner K).inner
      continuous_normalVector_real.continuousOn,
    (continuousOn_derivWithin_capInnerCorner K).inner
      lipschitzWith_tangentVector_real.continuous.continuousOn⟩

/-- The corner density is bounded, being continuous on the two compact halves of the cap domain
and zero outside. -/
theorem exists_bound_capCornerDensity (K : SpecialCapSpace) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, capCornerDensity K s ≤ C := by
  obtain ⟨hα, hβ⟩ := continuousOn_capVelocityCoefficients K
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hα
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hβ
  refine ⟨max (max C₁ C₂) 0, le_max_right _ _, fun s ↦ ?_⟩
  rw [capCornerDensity]
  split_ifs with h1 h2
  · exact le_max_of_le_left (le_max_of_le_right
      ((le_abs_self _).trans (hC₂ s ⟨h1.1.le, h1.2⟩)))
  · refine le_max_of_le_left (le_max_of_le_left ?_)
    have h := neg_le_abs (capVelocityCoefficients K (s - Real.pi / 2)).1
    exact h.trans (hC₁ _ ⟨by linarith [h2.1], by linarith [h2.2]⟩)
  · exact le_max_right _ _

/-! ### Finiteness and atomlessness of the corner measure -/

instance isFiniteMeasure_capCornerMeasure (K : SpecialCapSpace) :
    IsFiniteMeasure (capCornerMeasure K) := by
  obtain ⟨C, -, hC⟩ := exists_bound_capCornerDensity K
  refine ⟨?_⟩
  rw [capCornerMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc ∫⁻ s, ENNReal.ofReal (capCornerDensity K s) ∂volume.restrict (Set.Icc 0 Real.pi)
      ≤ ∫⁻ _, ENNReal.ofReal C ∂volume.restrict (Set.Icc 0 Real.pi) :=
        lintegral_mono fun s ↦ ENNReal.ofReal_le_ofReal (hC s)
    _ < ⊤ := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

instance isFiniteMeasure_capCornerAngleMeasure (K : SpecialCapSpace) :
    IsFiniteMeasure (capCornerAngleMeasure K) := by
  rw [capCornerAngleMeasure]
  exact Measure.isFiniteMeasure_map _ _

instance nullSingletonClass_capCornerAngleMeasure (K : SpecialCapSpace) :
    NullSingletonClass (capCornerAngleMeasure K) := by
  refine ⟨fun x ↦ ?_⟩
  rw [capCornerAngleMeasure,
    Measure.map_apply Real.Angle.continuous_coe.measurable (measurableSet_singleton x),
    capCornerMeasure]
  exact ((withDensity_absolutelyContinuous _ _).trans
    Measure.restrict_le_self.absolutelyContinuous)
    ((Real.Angle.countable_preimage_coe_singleton x).measure_zero volume)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Corner Paths
-/

public section

noncomputable section

namespace MovingSofa

/-- The inner-corner path restricted and bundled as a continuous BV path. -/
@[expose]
def capCornerBV (K : SpecialCapSpace) {a b : ℝ}
    (h : Set.Icc a b ⊆ Set.Icc 0 (Real.pi / 2)) : ContinuousBVPaths a b :=
  continuousBVOfContDiffOn (capInnerCorner K.val) (K.property.1.2.1.mono h)

/-- The corner BV path between the two reflected Gerver switching angles. -/
@[expose]
def capMiddleBV (K : SpecialCapSpace) :
    ContinuousBVPaths paperGerverConstants.2.1 paperGerverConstants.2.2 :=
  capCornerBV K (by
    have hφ : 0 ≤ GerversSofa.φ := GerversSofa.ABφθSpec.existsUnique.choose_spec.1.1
    intro t ht
    change GerversSofa.φ ≤ t ∧ t ≤ Real.pi / 2 - GerversSofa.φ at ht
    exact ⟨le_trans hφ ht.1, by linarith [ht.2]⟩)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Tail / Canonical
-/

public section

noncomputable section

namespace MovingSofa

/-- The closed half-planes above the right and left inner supporting walls. -/
@[expose]
def innerWallUpperHalfPlanes (K : RightAngleCapSpace) (t : ℝ) : Set Point × Set Point :=
  (normalHalfPlane (t : Real.Angle) (supportValue K.1 (t : Real.Angle) - 1) true false,
    normalHalfPlane ((t + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue K.1 ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) true false)

/-- The right and left canonical tail sets, before bundling their convex-body proofs. -/
@[expose]
def canonicalTailSets (K : SpecialCapSpace) : Set Point × Set Point :=
  ((K.1.1 : Set Point) ∩
      ⋂ t ∈ Set.Icc paperGerverConstants.2.1 (Real.pi / 2),
        (innerWallUpperHalfPlanes K.1 t).1,
    (K.1.1 : Set Point) ∩
      ⋂ t ∈ Set.Icc (0 : ℝ) paperGerverConstants.2.2,
        (innerWallUpperHalfPlanes K.1 t).2)

end MovingSofa

end

end

end

end

end

end
