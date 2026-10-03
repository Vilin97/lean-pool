/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle006
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle032
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle002
public import Mathlib.Analysis.Normed.Affine.ContinuousAffineMap
/-!
# Gerver sofa: related certificate and semantic modules

* `GerverSofa.KernelOnly.PartF.Semantics.Batch002`.
-/

public section

noncomputable section

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartF.F01ExistingMotion`.
* `KernelOnly.PartF.F01ParameterChoice`.
* `KernelOnly.PartF.F02EuclideanMotion`.
* `KernelOnly.PartF.F03CanonicalRotation`.
* `KernelOnly.PartF.F03SetIdentification`.
* `KernelOnly.PartF.F04IntegralRepresentation`.
* `KernelOnly.PartF.F06ParameterIdentification`.
* `KernelOnly.PartF.F06IntegralMotion`.
-/

public section

noncomputable section

section

/-!
# F01: exact identity normalization of the already certified motion

The original project asks for an initial translation. For its concrete
Gerver path the inverse frame is exactly the identity, which is the
stronger normalization required by DeepMind. These statements refer to
the existing `ℝ × ℝ` coordinate model, not to an unproved isometry between
the product norm and the Euclidean norm.
-/

public section

noncomputable section

namespace GerverSofa.PartF.Existing

/-- Invert the hallway frame to obtain the sofa’s rigid motion. -/
def motion (s : ℝ) : SE2 := (PartC.frame s).inv

theorem motion_zero : motion 0 = SE2.one := by
  change (Romik.frame PartC.params 0).inv = SE2.one
  simp [Romik.frame, Romik.angle, PartC.pathZero, SE2.inv, SE2.one]

theorem motion_continuous : SE2.ContinuousPath motion :=
  SE2.continuousPath_inv PartC.frameContinuous

theorem initial : PartC.G ⊆ horizontalArm := by
  intro q hq
  have h := PartC.initialArm ⟨q, hq, rfl⟩
  change (motion 0).act q ∈ horizontalArm at h
  rw [motion_zero, SE2.one_act] at h
  exact h

theorem all_times :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, (motion s).act '' PartC.G ⊆ hallway := by
  intro s hs
  exact inv_image_subset_hallway_of_subset_supporting
    (PartC.frame s) PartC.G (PartC.G_subset_hallway s hs)

theorem final : (motion 1).act '' PartC.G ⊆ verticalArm := PartC.finalArm

end GerverSofa.PartF.Existing

end

end

end

section

/-!
# F01: parameter selection is independent of the existence proof

This module reuses the frozen E24KC6 theorem. It does not repeat numerical
exclusion. The literal upstream order of conjunctions is checked against
the existing specification, and its selected tuple is identified with the
certified reduced solution. No identification with the full 22D tuple is
claimed by this module.
-/

public section

noncomputable section

namespace GerverSofa.PartF.Parameters

/-- The nonnegative parameter and ordered-angle equations used by the upstream canonical
definition. -/
@[expose]
def upstreamSpec (A B φ θ : ℝ) : Prop :=
  0 ≤ φ ∧ φ ≤ θ ∧ θ ≤ Real.pi / 4 ∧ 0 ≤ A ∧ 0 ≤ B ∧
  A * (θ.cos - φ.cos) - 2 * B * φ.sin
    + (θ - φ - 1) * θ.cos - θ.sin + φ.cos + φ.sin = 0 ∧
  A * (3 * θ.sin + φ.sin) - 2 * B * φ.cos
    + 3 * (θ - φ - 1) * θ.sin + 3 * θ.cos - φ.sin + φ.cos = 0 ∧
  A * φ.cos - (φ.sin + 1 / 2 - φ.cos / 2 + B * φ.sin) = 0 ∧
  (A + Real.pi / 2 - φ - θ) -
    (B - (θ - φ) * (1 + A) / 2 - (θ - φ)^2 / 4) = 0

theorem upstreamSpec_iff (A B φ θ : ℝ) :
    upstreamSpec A B φ θ ↔ PartE.DeepMindABPhiThetaSpec A B φ θ := by
  unfold upstreamSpec PartE.DeepMindABPhiThetaSpec PartE.PhysicalDomain
    PartE.reducedParams PartE.DeepMindEquations
  dsimp only
  tauto

/-- Package the upstream four-parameter specification as a predicate on a nested tuple. -/
@[expose]
def TupleSpec (q : ℝ × ℝ × ℝ × ℝ) : Prop :=
  upstreamSpec q.1 q.2.1 q.2.2.1 q.2.2.2

theorem existsUnique : ∃! q, TupleSpec q := by
  simpa only [TupleSpec, upstreamSpec_iff] using PartE.deepMindABPhiTheta_existsUnique

/-- The certified reduced solution converted to the upstream four-parameter tuple. -/
@[expose]
def certified : ℝ × ℝ × ℝ × ℝ :=
  PartE.tupleEquiv.symm PartALeanCert.reducedCertifiedUniqueSolution.solution

theorem certified_spec : TupleSpec certified := by
  apply (upstreamSpec_iff _ _ _ _).2
  exact PartE.deepMindSpec_of_mem_reducedBox_and_equations
    PartALeanCert.reducedCertifiedUniqueSolution.solution_mem
    PartALeanCert.reducedCertifiedUniqueSolution.satisfies

theorem any_solution_eq_certified (q : ℝ × ℝ × ℝ × ℝ) (hq : TupleSpec q) :
    q = certified := existsUnique.unique hq certified_spec

/-- This applies to any eventual upstream proof of the *same* specification. -/
theorem choice_independent (h : ∃! q, TupleSpec q) : h.choose = certified :=
  any_solution_eq_certified h.choose h.choose_spec.1

end GerverSofa.PartF.Parameters

end

end

end

section

/-!
# F02: the certified sofa as a set with Euclidean rigid motion

Every existing `SE2` action is realized by an affine isometry of `Plane`.
Norm preservation is proved in `Plane` from the equation `c*c+s*s=1`.
Continuity is proved in the induced continuous-affine-map topology of F01.
The final theorem transfers all seven motion fields for the already
certified set, without adding geometric hypotheses.

This module does not identify the set with the literal upstream integral
definition. Its rotation matrices are explicit; their comparison with
`F01.rotation` and the integral representation are separate bridge steps.
-/

public section

noncomputable section
open scoped unitInterval
namespace GerverSofa.PartF.EuclideanMotion

open Coordinates

/-- The standard rotation matrix associated with an existing `SE2` value. -/
@[expose]
def linearPart (g : SE2) : Plane ≃ₗ[ℝ] Plane where
  toFun := fun q => toPlane (g.c * q 0 - g.s * q 1, g.s * q 0 + g.c * q 1)
  invFun := fun q => toPlane (g.c * q 0 + g.s * q 1, -g.s * q 0 + g.c * q 1)
  left_inv := by
    intro q
    apply plane_ext
    · change g.c * (g.c * q 0 - g.s * q 1) +
        g.s * (g.s * q 0 + g.c * q 1) = q 0
      linear_combination (q 0) * g.unit
    · change -g.s * (g.c * q 0 - g.s * q 1) +
        g.c * (g.s * q 0 + g.c * q 1) = q 1
      linear_combination (q 1) * g.unit
  right_inv := by
    intro q
    apply plane_ext
    · change g.c * (g.c * q 0 + g.s * q 1) -
        g.s * (-g.s * q 0 + g.c * q 1) = q 0
      linear_combination (q 0) * g.unit
    · change g.s * (g.c * q 0 + g.s * q 1) +
        g.c * (-g.s * q 0 + g.c * q 1) = q 1
      linear_combination (q 1) * g.unit
  map_add' := by
    intro q r
    apply plane_ext
    · change g.c * (q 0 + r 0) - g.s * (q 1 + r 1) =
        (g.c * q 0 - g.s * q 1) + (g.c * r 0 - g.s * r 1)
      ring
    · change g.s * (q 0 + r 0) + g.c * (q 1 + r 1) =
        (g.s * q 0 + g.c * q 1) + (g.s * r 0 + g.c * r 1)
      ring
  map_smul' := by
    intro c q
    apply plane_ext
    · change g.c * (c * q 0) - g.s * (c * q 1) = c * (g.c * q 0 - g.s * q 1)
      ring
    · change g.s * (c * q 0) + g.c * (c * q 1) = c * (g.s * q 0 + g.c * q 1)
      ring

@[simp] theorem linearPart_zero_coord (g : SE2) (q : Plane) :
    linearPart g q 0 = g.c * q 0 - g.s * q 1 := rfl

@[simp] theorem linearPart_one_coord (g : SE2) (q : Plane) :
    linearPart g q 1 = g.s * q 0 + g.c * q 1 := rfl

theorem linearPart_norm_sq (g : SE2) (q : Plane) :
    ‖linearPart g q‖ ^ 2 = ‖q‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two]
  change (g.c * q 0 - g.s * q 1) ^ 2 + (g.s * q 0 + g.c * q 1) ^ 2 =
    (q 0) ^ 2 + (q 1) ^ 2
  linear_combination ((q 0) ^ 2 + (q 1) ^ 2) * g.unit

theorem linearPart_norm (g : SE2) (q : Plane) : ‖linearPart g q‖ = ‖q‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (linearPart_norm_sq g q)

/-- The linear isometry determined by the rotation coefficients of an SE2 motion. -/
@[expose]
def linearIsometry (g : SE2) : Plane ≃ₗᵢ[ℝ] Plane where
  toLinearEquiv := linearPart g
  norm_map' := linearPart_norm g

/-- A genuine Euclidean affine isometry with the original coordinate action. -/
@[expose]
def ofSE2 (g : SE2) : Rigid :=
  rotateThenTranslate (linearIsometry g) (toPlane (g.tx, g.ty))

theorem ofSE2_apply (g : SE2) (q : Plane) :
    ofSE2 g q = toPlane (g.act (fromPlane q)) := by
  exact plane_ext rfl rfl

theorem ofSE2_apply_toPlane (g : SE2) (q : Point) :
    ofSE2 g (toPlane q) = toPlane (g.act q) := by
  rw [ofSE2_apply, fromPlane_toPlane]

theorem ofSE2_one : ofSE2 SE2.one = AffineIsometryEquiv.refl ℝ Plane := by
  apply AffineIsometryEquiv.ext
  intro q
  change ofSE2 SE2.one q = q
  rw [ofSE2_apply, SE2.one_act, toPlane_fromPlane]

theorem image_action (g : SE2) (S : Set Point) :
    ofSE2 g '' (toPlane '' S) = toPlane '' (g.act '' S) := by
  simp only [Set.image_image, ofSE2_apply_toPlane]

/-- The coordinate quarter-turn, used to express continuous matrix coefficients. -/
def quarterTurnLinear : Plane →ₗ[ℝ] Plane where
  toFun := fun q => toPlane (-q 1, q 0)
  map_add' := by
    intro q r
    apply plane_ext
    · change -(q 1 + r 1) = -q 1 + -r 1
      ring
    · rfl
  map_smul' := by
    intro c q
    apply plane_ext
    · change -(c * q 1) = c * (-q 1)
      ring
    · rfl

/-- The quarter-turn rotation bundled as a continuous linear map. -/
def quarterTurn : Plane →L[ℝ] Plane := quarterTurnLinear.toContinuousLinearMap

/-- Componentwise continuous `SE2` coefficients give continuity in the
actual topology on affine isometry equivalences. -/
theorem continuous_ofSE2 {X : Type*} [TopologicalSpace X]
    (g : X → SE2)
    (hc : Continuous (fun t => (g t).c))
    (hs : Continuous (fun t => (g t).s))
    (htx : Continuous (fun t => (g t).tx))
    (hty : Continuous (fun t => (g t).ty)) :
    Continuous (fun t => ofSE2 (g t)) := by
  let lin : X → (Plane →L[ℝ] Plane) := fun t =>
    (g t).c • ContinuousLinearMap.id ℝ Plane + (g t).s • quarterTurn
  let offset : X → Plane := fun t => toPlane ((g t).tx, (g t).ty)
  let D := ContinuousAffineMap.decompLinearIsometryEquiv ℝ ℝ Plane Plane
  have hlin : Continuous lin :=
    (hc.smul continuous_const).add (hs.smul continuous_const)
  have hoffset : Continuous offset := continuous_toPlane.comp (htx.prodMk hty)
  have hD : Continuous (fun t => D.symm (offset t, lin t)) :=
    D.symm.continuous.comp (hoffset.prodMk hlin)
  apply continuous_induced_rng.mpr
  change Continuous (fun t => (ofSE2 (g t)).toAffineIsometry.toContinuousAffineMap)
  have heq :
      (fun t => (ofSE2 (g t)).toAffineIsometry.toContinuousAffineMap) =
      (fun t => D.symm (offset t, lin t)) := by
    funext t
    apply ContinuousAffineMap.ext
    intro q
    change ofSE2 (g t) q = D.symm (offset t, lin t) q
    dsimp only [D]
    rw [ContinuousAffineMap.decompLinearIsometryEquiv_symm_apply, ofSE2_apply]
    apply plane_ext
    · change (g t).c * q 0 - (g t).s * q 1 + (g t).tx =
        (g t).c * q 0 + (g t).s * (-q 1) + (g t).tx
      ring
    · change (g t).s * q 0 + (g t).c * q 1 + (g t).ty =
        (g t).c * q 1 + (g t).s * q 0 + (g t).ty
      ring
  rw [heq]
  exact hD

theorem continuous_ofSE2_path (g : ℝ → SE2) (hg : SE2.ContinuousPath g) :
    Continuous (fun t => ofSE2 (g t)) := by
  rcases hg with ⟨hc, hs, htx, hty⟩
  exact continuous_ofSE2 g hc hs htx hty

/-- The coordinate image of the certified Gerver sofa in the Euclidean plane. -/
def sofa : Set Plane := toPlane '' PartC.G

/-- The certified sofa motion as affine isometries indexed by the unit interval. -/
def motion (s : I) : Rigid := ofSE2 (Existing.motion (s : ℝ))

theorem motion_continuous : Continuous motion :=
  (continuous_ofSE2_path Existing.motion Existing.motion_continuous).comp continuous_subtype_val

/-- All seven motion requirements hold for the coordinate image of the
already certified Gerver set. No additional geometric assumptions occur. -/
theorem concrete_movingSofa : Model.IsMovingSofa sofa motion := by
  refine ⟨?_, ?_, motion_continuous, ?_, ?_, ?_, ?_⟩
  · exact isConnected_image PartC.Stage4.globalGeometryCertificate.connected
  · exact isClosed_image PartC.closed_G
  · change ofSE2 (Existing.motion 0) = AffineIsometryEquiv.refl ℝ Plane
    rw [Existing.motion_zero, ofSE2_one]
  · change toPlane '' PartC.G ⊆ Model.horizontalHallway
    rw [← horizontal_image]
    exact Set.image_mono Existing.initial
  · intro s
    change ofSE2 (Existing.motion (s : ℝ)) '' (toPlane '' PartC.G) ⊆ Model.hallway
    rw [image_action, ← hallway_image]
    exact Set.image_mono (Existing.all_times (s : ℝ) s.property)
  · change ofSE2 (Existing.motion 1) '' (toPlane '' PartC.G) ⊆ Model.verticalHallway
    rw [image_action, ← vertical_image]
    exact Set.image_mono Existing.final

end GerverSofa.PartF.EuclideanMotion

end

end

end

section

/-!
# F03: the upstream-oriented rotation in the certified coordinates

The orientation is the ordered coordinate-basis orientation installed in F01,
with the same definition as the pinned upstream plane helper. We compute its
area form, then its right-angle rotation, before comparing rotation matrices.
No replacement orientation or additional orientation hypothesis is introduced.
-/

public section

noncomputable section
namespace GerverSofa.PartF.CanonicalRotation

open Coordinates EuclideanMotion

/-- The sign is fixed by the ordered orthonormal coordinate basis. -/
theorem areaForm_coordinates (q r : Plane) :
    EuclideanGeometry.o.areaForm q r = q 0 * r 1 - q 1 * r 0 := by
  rw [Orientation.areaForm_to_volumeForm,
    EuclideanGeometry.o.volumeForm_robust (EuclideanSpace.basisFun (Fin 2) ℝ) rfl,
    Module.Basis.det_apply]
  simp [Module.Basis.toMatrix, Matrix.det_fin_two, mul_comm]

/-- The positive quarter-turn is exactly `(x,y) ↦ (-y,x)`. -/
theorem rightAngleRotation_apply (q : Plane) :
    EuclideanGeometry.o.rightAngleRotation q = toPlane (-q 1, q 0) := by
  apply plane_ext
  · have h := EuclideanGeometry.o.inner_rightAngleRotation_left q
      (EuclideanSpace.basisFun (Fin 2) ℝ 0)
    rw [EuclideanSpace.inner_basisFun_real, areaForm_coordinates] at h
    simpa [EuclideanSpace.basisFun_apply, PiLp.single_apply] using h
  · have h := EuclideanGeometry.o.inner_rightAngleRotation_left q
      (EuclideanSpace.basisFun (Fin 2) ℝ 1)
    rw [EuclideanSpace.inner_basisFun_real, areaForm_coordinates] at h
    simpa [EuclideanSpace.basisFun_apply, PiLp.single_apply] using h

theorem rotation_apply (t : ℝ) (q : Plane) :
    rotation t q = toPlane (Romik.rot t (fromPlane q)) := by
  change EuclideanGeometry.o.rotation (t : Real.Angle) q = _
  rw [Orientation.rotation_apply, rightAngleRotation_apply]
  simp only [Real.Angle.cos_coe, Real.Angle.sin_coe]
  apply plane_ext
  · change Real.cos t * q 0 + Real.sin t * (-q 1) =
      Real.cos t * q 0 - Real.sin t * q 1
    ring
  · change Real.cos t * q 1 + Real.sin t * q 0 =
      Real.sin t * q 0 + Real.cos t * q 1
    ring

theorem rotation_toPlane (t : ℝ) (q : Point) :
    rotation t (toPlane q) = toPlane (Romik.rot t q) := by
  rw [rotation_apply, fromPlane_toPlane]

theorem linearIsometry_eq_rotation (g : SE2) (t : ℝ)
    (hc : g.c = Real.cos t) (hs : g.s = Real.sin t) :
    linearIsometry g = rotation t := by
  apply LinearIsometryEquiv.ext
  intro q
  rw [rotation_apply]
  change toPlane (g.c * q 0 - g.s * q 1, g.s * q 0 + g.c * q 1) =
    toPlane (Real.cos t * q 0 - Real.sin t * q 1,
      Real.sin t * q 0 + Real.cos t * q 1)
  rw [hc, hs]

theorem ofSE2_eq_worldFrame (g : SE2) (t : ℝ)
    (hc : g.c = Real.cos t) (hs : g.s = Real.sin t) :
    ofSE2 g = worldFrame t (toPlane (g.tx, g.ty)) := by
  unfold ofSE2 worldFrame
  rw [linearIsometry_eq_rotation g t hc hs]

/-- The physical angle is `s * (π/2)`, including both endpoints. -/
theorem romikFrame_eq_worldFrame (p : Romik.Params) (s : ℝ) :
    ofSE2 (Romik.frame p s) =
      worldFrame (Romik.angle s) (toPlane (Romik.path p (Romik.angle s))) := by
  exact ofSE2_eq_worldFrame (Romik.frame p s) (Romik.angle s) rfl rfl

theorem romikFrame_zero_act (p : Romik.Params)
    (hzero : Romik.path p 0 = (0, 0)) (q : Point) :
    (Romik.frame p 0).act q = q := by
  simp [Romik.frame, Romik.angle, hzero, SE2.act]

/-- The already proved five-phase algebra now uses the canonical rotation. -/
theorem closedPath_rotation (d : Reduced.Params)
    (hd : Reduced.Equations d) (t : ℝ) :
    rotation t (toPlane (Phases.closedPath d t)) =
      toPlane (Romik.path (Phases.dictionary d) t) := by
  rw [rotation_toPlane, Phases.fivePhaseRepresentation d hd t]

end GerverSofa.PartF.CanonicalRotation

end

end

end

section

/-!
# F03: the certified set as a canonical hallway intersection

We transport the existing reconstruction theorem, including the endpoint arms,
to the Euclidean world-frame convention. The final conditional interfaces state
the outstanding path/dictionary equalities explicitly. They do not prove the
literal integral representation or identify the certified 22D tuple.
-/

public section

noncomputable section
open scoped unitInterval
namespace GerverSofa.PartF.SetIdentification

open Coordinates EuclideanMotion CanonicalRotation

theorem mem_coordinate_image (S : Set Point) (q : Plane) :
    q ∈ toPlane '' S ↔ fromPlane q ∈ S := by
  rw [image_eq_preimage]
  rfl

theorem mem_ofSE2_image (g : SE2) (S : Set Point) (q : Plane) :
    q ∈ ofSE2 g '' (toPlane '' S) ↔ fromPlane q ∈ g.act '' S := by
  rw [image_action, mem_coordinate_image]

/-- The change from real unit time to subtype unit time loses no constraint. -/
theorem reconstructedSet_image (p : Romik.Params)
    (hzero : Romik.path p 0 = (0, 0)) :
    toPlane '' Romik.reconstructedSet p =
      frameIntersection (fun s : I => ofSE2 (Romik.frame p (s : ℝ)))
        Model.horizontalHallway Model.verticalHallway Model.hallway := by
  have hstart : (Romik.frame p 0).act '' horizontalArm = horizontalArm := by
    have hfun : (Romik.frame p 0).act = id :=
      funext (romikFrame_zero_act p hzero)
    rw [hfun, Set.image_id]
  ext q
  simp only [frameIntersection, ← horizontal_image, ← vertical_image,
    ← hallway_image, Set.mem_inter_iff, Set.mem_iInter,
    mem_ofSE2_image, mem_coordinate_image]
  change (fromPlane q ∈ horizontalArm ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1,
        fromPlane q ∈ (Romik.frame p s).act '' hallway) ∧
      fromPlane q ∈ (Romik.frame p 1).act '' verticalArm) ↔
    (fromPlane q ∈ (Romik.frame p 0).act '' horizontalArm ∧
      fromPlane q ∈ (Romik.frame p 1).act '' verticalArm) ∧
      ∀ s : I, fromPlane q ∈ (Romik.frame p (s : ℝ)).act '' hallway
  rw [hstart]
  constructor
  · rintro ⟨hi, hall, hf⟩
    exact ⟨⟨hi, hf⟩, fun s => hall (s : ℝ) s.property⟩
  · rintro ⟨⟨hi, hf⟩, hall⟩
    exact ⟨hi, fun s hs => hall ⟨s, hs⟩, hf⟩

theorem reconstructedSet_image_eq_worldSofa (p : Romik.Params)
    (hzero : Romik.path p 0 = (0, 0)) :
    toPlane '' Romik.reconstructedSet p =
      worldSofa (fun t => toPlane (Romik.path p t))
        Model.horizontalHallway Model.verticalHallway Model.hallway := by
  rw [reconstructedSet_image p hzero, worldSofa, angleIntersection_eq_frameIntersection]
  have hframes :
      (fun s : I => ofSE2 (Romik.frame p (s : ℝ))) =
      (fun s : I => worldFrame ((s : ℝ) * (Real.pi / 2))
        (toPlane (Romik.path p ((s : ℝ) * (Real.pi / 2))))) := by
    funext s
    exact romikFrame_eq_worldFrame p (s : ℝ)
  exact congrArg (fun F => frameIntersection F
    Model.horizontalHallway Model.verticalHallway Model.hallway) hframes

/-- An unconditional identification of the concrete, already certified set. -/
theorem sofa_eq_worldSofa :
    EuclideanMotion.sofa =
      worldSofa (fun t => toPlane (Romik.path PartC.params t))
        Model.horizontalHallway Model.verticalHallway Model.hallway := by
  change toPlane '' PartC.G = _
  rw [PartC.G_eq_Sx]
  exact reconstructedSet_image_eq_worldSofa PartC.params PartC.pathZero

end GerverSofa.PartF.SetIdentification

end

end

end

section

/-!
# F04: the literal integral path equals the closed five-phase path

All integral identities are proved in F04IntegralEvaluation. Reflection of the
closed intervals then gives the same five branches and the same endpoint choices
as F01. The final identification with PartC.params still requires the 22D
dictionary theorem; it remains an explicit hypothesis in the two last results.
-/

public section

noncomputable section
namespace GerverSofa.PartF.Integrals

open Phases Coordinates

theorem path_first_of_le (d : Reduced.Params) (t : ℝ) (ht : t ≤ d.phi) :
    (path d t).1 = Real.cos t - 1 := by
  simp only [path, ite_eq_left ht]

theorem path_first_of_gt (d : Reduced.Params) (t : ℝ) (ht : d.phi < t) :
    (path d t).1 = W d (T - t) - 1 := by
  simp only [path, ite_eq_right (not_le.mpr ht)]
  unfold W
  dsimp only [T]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]

theorem path_second_of_le (d : Reduced.Params) (ho : Ordered d)
    (hd : Reduced.Equations d) (t : ℝ) (ht : t ≤ tau d) :
    (path d t).2 = W d t - ell d * Real.sin t - 1 := by
  simp only [path, ite_eq_left ht]
  rw [xi_zero d ho hd]
  unfold W ell
  ring

theorem path_second_of_gt (d : Reduced.Params) (ho : Ordered d)
    (hd : Reduced.Equations d) (t : ℝ) (ht : tau d < t) :
    (path d t).2 = (1 - ell d) * Real.sin t - 1 := by
  simp only [path, ite_eq_right (not_le.mpr ht)]
  rw [xi_zero d ho hd]
  unfold ell
  ring

theorem path_phase1 (d : Reduced.Params) (ho : Ordered d)
    (hd : Reduced.Equations d) (t : ℝ) (ht : t ∈ Set.Icc 0 d.phi) :
    path d t = closed1 d t := by
  have hk := ordered_knots d ho
  have htau : t ≤ tau d := ht.2.trans (hk.2.1.trans (hk.2.2.1.trans hk.2.2.2.1))
  apply Prod.ext
  · exact path_first_of_le d t ht.2
  · rw [path_second_of_le d ho hd t htau, W_phase1 d ho hd t ht, U1_eq_half d hd]
    dsimp [closed1, r1]
    ring

theorem path_phase2 (d : Reduced.Params) (ho : Ordered d)
    (hd : Reduced.Equations d) (t : ℝ)
    (hlo : d.phi < t) (hhi : t ≤ d.theta) : path d t = closed2 d t := by
  have hk := ordered_knots d ho
  have hr : T - t ∈ Set.Icc (eta d) (tau d) := by
    dsimp [eta, tau]
    constructor <;> linarith
  have htau : t ≤ tau d := hhi.trans (hk.2.2.1.trans hk.2.2.2.1)
  apply Prod.ext
  · rw [path_first_of_gt d t hlo, W_phase4 d ho (T - t) hr]
    simp only [closed2, T, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  · rw [path_second_of_le d ho hd t htau, W_phase2 d ho hd t ⟨hlo.le, hhi⟩]
    dsimp [closed2, U2]
    ring

theorem path_phase3 (d : Reduced.Params) (ho : Ordered d)
    (hd : Reduced.Equations d) (t : ℝ)
    (hlo : d.theta < t) (hhi : t ≤ eta d) : path d t = closed3 d t := by
  have hk := ordered_knots d ho
  have hphi : d.phi < t := lt_of_le_of_lt ho.2.1 hlo
  have hr : T - t ∈ Set.Icc d.theta (eta d) := by
    dsimp [eta] at *
    constructor <;> linarith
  have htau : t ≤ tau d := hhi.trans hk.2.2.2.1
  apply Prod.ext
  · rw [path_first_of_gt d t hphi, W_phase3 d ho hd (T - t) hr]
    simp only [closed3, T, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  · rw [path_second_of_le d ho hd t htau, W_phase3 d ho hd t ⟨hlo.le, hhi⟩]
    dsimp [closed3]
    ring

theorem path_phase4 (d : Reduced.Params) (ho : Ordered d)
    (hd : Reduced.Equations d) (t : ℝ)
    (hlo : eta d < t) (hhi : t ≤ tau d) : path d t = closed4 d t := by
  have hk := ordered_knots d ho
  have hphi : d.phi < t := lt_of_le_of_lt (ho.2.1.trans hk.2.2.1) hlo
  have hr : T - t ∈ Set.Icc d.phi d.theta := by
    dsimp [eta, tau] at *
    constructor <;> linarith
  apply Prod.ext
  · rw [path_first_of_gt d t hphi, W_phase2 d ho hd (T - t) hr]
    simp only [closed4, U2, T, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  · rw [path_second_of_le d ho hd t hhi, W_phase4 d ho t ⟨hlo.le, hhi⟩]
    dsimp [closed4]
    ring

theorem path_phase5 (d : Reduced.Params) (ho : Ordered d)
    (hd : Reduced.Equations d) (t : ℝ)
    (hlo : tau d < t) (hhi : t ≤ T) : path d t = closed5 d t := by
  have hk := ordered_knots d ho
  have hphi : d.phi < t :=
    lt_of_le_of_lt (ho.2.1.trans (hk.2.2.1.trans hk.2.2.2.1)) hlo
  have hr : T - t ∈ Set.Icc 0 d.phi := by
    dsimp [tau] at *
    constructor <;> linarith
  apply Prod.ext
  · rw [path_first_of_gt d t hphi, W_phase1 d ho hd (T - t) hr, U1_eq_half d hd]
    dsimp only [closed5, r1, T]
    rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    ring
  · exact path_second_of_gt d ho hd t hlo

/-- The literal integral path, not just its formal candidate, has these phases. -/
theorem path_eq_closedPath (d : Reduced.Params) (ho : Ordered d)
    (hd : Reduced.Equations d) (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    path d t = closedPath d t := by
  change path d t =
    (if t ≤ d.phi then closed1 d t
     else if t ≤ d.theta then closed2 d t
     else if t ≤ eta d then closed3 d t
     else if t ≤ tau d then closed4 d t
     else closed5 d t)
  by_cases h1 : t ≤ d.phi
  · simpa only [ite_eq_left h1] using path_phase1 d ho hd t ⟨ht.1, h1⟩
  by_cases h2 : t ≤ d.theta
  · simpa only [ite_eq_right h1, ite_eq_left h2] using path_phase2 d ho hd t (lt_of_not_ge h1) h2
  by_cases h3 : t ≤ eta d
  · simpa only [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3] using
      path_phase3 d ho hd t (lt_of_not_ge h2) h3
  by_cases h4 : t ≤ tau d
  · simpa only [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4] using
      path_phase4 d ho hd t (lt_of_not_ge h3) h4
  · simpa only [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4] using
      path_phase5 d ho hd t (lt_of_not_ge h4) ht.2

theorem integral_rotation (d : Reduced.Params) (ho : Ordered d)
    (hd : Reduced.Equations d) (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    rotation t (toPlane (path d t)) = toPlane (Romik.path (dictionary d) t) := by
  rw [path_eq_closedPath d ho hd t ht, CanonicalRotation.closedPath_rotation d hd t]

theorem integral_sofa_eq_worldSofa (d : Reduced.Params) (ho : Ordered d)
    (hd : Reduced.Equations d) :
    bodySofa (fun t => toPlane (path d t))
        Model.horizontalHallway Model.verticalHallway Model.hallway =
      worldSofa (fun t => toPlane (Romik.path (dictionary d) t))
        Model.horizontalHallway Model.verticalHallway Model.hallway := by
  apply bodySofa_eq_worldSofa_of_path_identity
  intro t ht
  exact (integral_rotation d ho hd t ht).symm

/-- The reduced parameters selected by the concrete uniqueness certificate. -/
@[expose]
def certified : Reduced.Params := PartALeanCert.reducedCertifiedUniqueSolution.solution

theorem certified_ordered : Ordered certified := by
  have h := PartE.physicalDomain_of_mem_reducedBox
    PartALeanCert.reducedCertifiedUniqueSolution.solution_mem
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem certified_equations : Reduced.Equations certified :=
  PartALeanCert.reducedCertifiedUniqueSolution.satisfies

/-- An unconditional representation theorem for the certified reduced tuple. -/
theorem certified_integral_rotation (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    rotation t (toPlane (path certified t)) =
      toPlane (Romik.path (dictionary certified) t) :=
  integral_rotation certified certified_ordered certified_equations t ht

/-- Remaining obligation: identify the full dictionary with the independent 22D root. -/
theorem integral_sofa_eq_certified_of_dictionary
    (hdictionary : dictionary certified = PartC.params) :
    bodySofa (fun t => toPlane (path certified t))
        Model.horizontalHallway Model.verticalHallway Model.hallway =
      EuclideanMotion.sofa := by
  rw [integral_sofa_eq_worldSofa certified certified_ordered certified_equations,
    hdictionary, ← SetIdentification.sofa_eq_worldSofa]

end GerverSofa.PartF.Integrals

end

end

end

section

/-!
# F06: identify the two independently certified parameter choices

The 22D box supplies only coarse physical inequalities for its reverse
parameters. Global 4D uniqueness from Part E then identifies the reduced root.
The full algebraic reconstruction closes the 22D identity without a new
Krawczyk run or a forward enclosure into the narrow full box.
-/

public section

noncomputable section
namespace GerverSofa.PartF.Parameters

open Phases

theorem undictionary_physical_of_mem_full_box {p : Romik.Params}
    (hp : p ∈ Romik.box) : PartE.PhysicalDomain (undictionary p) := by
  dsimp [Romik.box, qR] at hp
  rcases hp with ⟨_, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _,
    hb1lo, hb1hi, hb2lo, _, _, _, _, _,
    _, _, _, _, _, _, _, _,
    hphilo, hphihi, hthetalo, hthetahi⟩
  norm_num at hb1lo hb1hi hb2lo hphilo hphihi hthetalo hthetahi
  have hphi0 : 0 ≤ p.phi := by linarith only [hphilo]
  have hphi1 : p.phi ≤ 1 / 20 := by linarith only [hphihi]
  have htheta0 : (3 / 5 : ℝ) ≤ p.theta := by linarith only [hthetalo]
  have htheta1 : p.theta ≤ 7 / 10 := by linarith only [hthetahi]
  change 0 ≤ p.phi ∧ p.phi ≤ p.theta ∧ p.theta ≤ Real.pi / 4 ∧
    0 ≤ p.phi - 1 - 2 * p.b1 ∧
    0 ≤ p.b2 + 1 / 2 - (1 + (p.phi - 1 - 2 * p.b1)) * p.phi / 2 + p.phi ^ 2 / 4
  refine ⟨hphi0, ?_, ?_, ?_, ?_⟩
  · linarith only [hphi1, htheta0]
  · nlinarith only [htheta1, Real.pi_gt_three]
  · linarith only [hphi0, hb1hi]
  · have hprod : 0 ≤ (p.b1 + 3 / 5) * p.phi :=
      mul_nonneg (by linarith only [hb1lo]) hphi0
    have hsq : 0 ≤ p.phi * (1 / 20 - p.phi) :=
      mul_nonneg hphi0 (by linarith only [hphi1])
    nlinarith only [hb2lo, hprod, hsq, hphi0, hphi1]

theorem undictionary_eq_reduced_certified {p : Romik.Params}
    (hp : p ∈ Romik.box) (heq : Romik.Equations p) :
    undictionary p = PartALeanCert.reducedCertifiedUniqueSolution.solution := by
  let d := undictionary p
  have hdom : PartE.PhysicalDomain d := undictionary_physical_of_mem_full_box hp
  have he : Reduced.Equations d := undictionary_equations heq
  have hspec : PartE.DeepMindABPhiThetaSpec d.a d.b d.phi d.theta :=
    (PartE.deepMindSpec_iff_physicalDomain_and_reducedEquations _ _ _ _).2 ⟨hdom, he⟩
  let q : ℝ × ℝ × ℝ × ℝ := (d.a, d.b, d.phi, d.theta)
  have hq : TupleSpec q := (upstreamSpec_iff _ _ _ _).2 hspec
  have htuple := any_solution_eq_certified q hq
  have hparams := congrArg PartE.tupleEquiv htuple
  rw [certified, PartE.tupleEquiv.apply_symm_apply] at hparams
  exact hparams

theorem dictionary_eq_full_certified :
    dictionary PartALeanCert.reducedCertifiedUniqueSolution.solution = PartB.params := by
  have hu := undictionary_eq_reduced_certified PartB.params_mem PartB.params_equations
  calc
    dictionary PartALeanCert.reducedCertifiedUniqueSolution.solution =
        dictionary (undictionary PartB.params) := congrArg dictionary hu.symm
    _ = PartB.params := dictionary_undictionary_of_equations PartB.params_equations

end GerverSofa.PartF.Parameters

end

end

end

section

/-!
# F06: unconditional motion bridge for the literal integral construction

This is the translate-then-rotate body model defined in Part F, with the
canonical Euclidean orientation. It does not silently replace the current
upstream rotateTranslate definition discussed in issue #5270.
-/

public section

noncomputable section
namespace GerverSofa.PartF.Integrals

open Phases Coordinates

theorem certified_dictionary_eq_params : dictionary certified = PartC.params :=
  Parameters.dictionary_eq_full_certified

theorem certified_integral_rotation_to_full (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    rotation t (toPlane (path certified t)) = toPlane (Romik.path PartC.params t) := by
  rw [certified_integral_rotation t ht, certified_dictionary_eq_params]

theorem integral_sofa_eq_certified :
    bodySofa (fun t => toPlane (path certified t))
        Model.horizontalHallway Model.verticalHallway Model.hallway =
      EuclideanMotion.sofa :=
  integral_sofa_eq_certified_of_dictionary certified_dictionary_eq_params

end GerverSofa.PartF.Integrals

end

end

end

end

end

end
