/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Setoid.Basic
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Topology.UnitInterval

/-!
# Polygonal quotient spaces

This file supplies the geometric foundation for realizing a finite surface cell complex. A
`PolygonCell n` is a genuinely indexed closed disk with `n` labelled boundary arcs. This
topological model keeps monogons and digons as genuine disks, unlike a convex hull of one or two
Euclidean vertices. Its sides are circular arcs; only their interval reparameterizations are
affine. A later PL bridge is therefore still needed if consumers require straight Euclidean edges.

For a family of cells, `PolygonGluing.PreRealization` is their disjoint union with the sum topology.
A set of `PolygonGluing.Identification`s prescribes either the identity or the affine reversal
`t ↦ 1 - t` between pairs of sides. `PolygonGluing.setoid` is the equivalence relation generated
by those point identifications, and `PolygonGluing.Realization` has the quotient topology.

`PolygonCell 0` is a disk with no marked sides. It is deliberately not identified with the
empty-word sphere. The cell-complex adapter therefore presents the sphere as two oppositely
oriented monogons instead of using `PolygonCell 0`. Keeping that choice out of this generic layer
prevents a side-free disk from silently acquiring the wrong topology.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

/-- A closed disk whose boundary is divided into `n` labelled sides. -/
structure PolygonCell (_n : ℕ) where
  /-- The `val` declaration. -/
  val : ℂ
  property : val ∈ Metric.closedBall (0 : ℂ) 1

namespace PolygonCell

instance (n : ℕ) : CoeOut (PolygonCell n) ℂ :=
  ⟨val⟩

@[ext]
theorem ext {n : ℕ} {x y : PolygonCell n} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  simp_all

noncomputable instance (n : ℕ) : TopologicalSpace (PolygonCell n) :=
  TopologicalSpace.induced val inferInstance

theorem continuous_val {n : ℕ} : Continuous (fun x : PolygonCell n => x.val) :=
  continuous_induced_dom

/-- The side count is marking data only: changing it does not change the underlying closed
disk. -/
noncomputable def castHomeomorph {m n : ℕ} (h : m = n) :
    PolygonCell m ≃ₜ PolygonCell n := by
  subst n
  exact Homeomorph.refl _

theorem castHomeomorph_val {m n : ℕ} (h : m = n) (x : PolygonCell m) :
    (castHomeomorph h x).val = x.val := by
  subst n
  rfl

/-- The unit circle included in a polygonal cell. -/
def ofCircle (n : ℕ) : C(Circle, PolygonCell n) where
  toFun z := ⟨z, by
    rw [Metric.mem_closedBall]
    exact z.property.le⟩
  continuous_toFun := continuous_induced_rng.2 continuous_subtype_val

/-- The angle swept out by side `i` at parameter `t`. -/
noncomputable def sideAngle {n : ℕ} (i : Fin n) (t : unitInterval) : ℝ :=
  2 * Real.pi * ((i.val : ℝ) + t) / n

theorem continuous_sideAngle {n : ℕ} (i : Fin n) : Continuous (sideAngle i) := by
  unfold sideAngle
  fun_prop

/-- Side `i` of an `n`-sided cell, parameterized in boundary order. -/
noncomputable def side {n : ℕ} (i : Fin n) : C(unitInterval, PolygonCell n) where
  toFun t := ofCircle n (Circle.exp (sideAngle i t))
  continuous_toFun :=
    (ofCircle n).continuous.comp (Circle.exp.continuous.comp (continuous_sideAngle i))

/-- Side `i` traversed in the opposite direction. -/
noncomputable def reversedSide {n : ℕ} (i : Fin n) : C(unitInterval, PolygonCell n) where
  toFun t := side i (unitInterval.symm t)
  continuous_toFun := (side i).continuous.comp unitInterval.continuous_symm

theorem reversedSide_apply {n : ℕ} (i : Fin n) (t : unitInterval) :
    reversedSide i t = side i (unitInterval.symm t) :=
  rfl

theorem castHomeomorph_side {m n : ℕ} (h : m = n) (i : Fin m)
    (t : unitInterval) :
    castHomeomorph h (side i t) = side (Fin.cast h i) t := by
  subst n
  rfl

theorem reversedSide_zero {n : ℕ} (i : Fin n) : reversedSide i 0 = side i 1 := by
  rw [reversedSide_apply]
  simp only [unitInterval.symm_zero]

@[simp]
theorem reversedSide_one {n : ℕ} (i : Fin n) : reversedSide i 1 = side i 0 := by
  rw [reversedSide_apply]
  simp only [unitInterval.symm_one]

/-- Consecutive sides meet at their common cyclic endpoint. -/
theorem side_one_eq_rotate_zero {n : ℕ} (i : Fin n) :
    side i 1 = side (finRotate n i) 0 := by
  apply PolygonCell.ext
  change (Circle.exp (sideAngle i 1) : ℂ) =
    (Circle.exp (sideAngle (finRotate n i) 0) : ℂ)
  apply congr_arg (fun z : Circle => (z : ℂ))
  apply Circle.exp_eq_exp.mpr
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt i.pos)
  by_cases hi : i = Fin.last n
  · subst i
    refine ⟨1, ?_⟩
    rw [finRotate_last]
    simp [sideAngle]
    field_simp
  · refine ⟨0, ?_⟩
    simp only [sideAngle, Nat.succ_eq_add_one, finRotate_apply, Int.cast_zero, zero_mul,
      add_zero]
    rw [Fin.val_add_one_of_lt (Fin.val_lt_last hi)]
    push_cast
    rw [add_zero]

/-- Every side lies on the boundary circle of its polygonal cell. -/
theorem side_mem_sphere {n : ℕ} (i : Fin n) (t : unitInterval) :
    (side i t : ℂ) ∈ Metric.sphere 0 1 := by
  exact (Circle.exp (sideAngle i t)).property

/-- Every boundary point of a cell with at least one side belongs to a marked side. -/
theorem exists_side_eq_of_mem_sphere {n : ℕ} (hn : 0 < n) (x : PolygonCell n)
    (hx : (x : ℂ) ∈ Metric.sphere 0 1) :
    ∃ i : Fin n, ∃ t : unitInterval, side i t = x := by
  let z : Circle := ⟨x.val, hx⟩
  obtain ⟨θ, hθ, hθeq⟩ :=
    Circle.periodic_exp.exists_mem_Ico₀ Real.two_pi_pos z.val.arg
  have hθz : Circle.exp θ = z := hθeq.symm.trans (Circle.exp_arg z)
  let r : ℝ := θ * n / (2 * Real.pi)
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact div_nonneg (mul_nonneg hθ.1 (Nat.cast_nonneg n)) Real.two_pi_pos.le
  have hr_lt : r < n := by
    dsimp [r]
    rw [div_lt_iff₀ Real.two_pi_pos]
    exact (mul_lt_mul_of_pos_right hθ.2 (Nat.cast_pos.2 hn)).trans_eq (mul_comm _ _)
  let i : Fin n := ⟨⌊r⌋₊, (Nat.floor_lt hr_nonneg).2 hr_lt⟩
  let t : unitInterval := ⟨r - ⌊r⌋₊, sub_nonneg.2 (Nat.floor_le hr_nonneg), by
    have ht : r - (⌊r⌋₊ : ℝ) < 1 := by
      rw [sub_lt_iff_lt_add]
      simpa only [add_comm] using Nat.lt_floor_add_one r
    exact ht.le⟩
  refine ⟨i, t, ?_⟩
  apply PolygonCell.ext
  change (Circle.exp (sideAngle i t) : ℂ) = x.val
  have hangle : sideAngle i t = θ := by
    dsimp [sideAngle, i, t, r]
    field_simp [hn.ne', Real.pi_ne_zero]
    ring
  rw [hangle, hθz]

/-- Boundary membership is equivalent to membership in one of the marked sides. -/
theorem mem_sphere_iff_exists_side {n : ℕ} (hn : 0 < n) (x : PolygonCell n) :
    (x : ℂ) ∈ Metric.sphere 0 1 ↔
      ∃ i : Fin n, ∃ t : unitInterval, side i t = x := by
  constructor
  · exact exists_side_eq_of_mem_sphere hn x
  · rintro ⟨i, t, rfl⟩
    exact side_mem_sphere i t

/-- The marked sides cover exactly the boundary circle of a nonzero-sided cell. -/
theorem iUnion_range_side {n : ℕ} (hn : 0 < n) :
    (⋃ i : Fin n, Set.range (side i)) =
      {x : PolygonCell n | (x : ℂ) ∈ Metric.sphere 0 1} := by
  ext x
  simpa only [Set.mem_iUnion, Set.mem_range, Set.mem_setOf_eq] using
    (mem_sphere_iff_exists_side hn x).symm

/-- The unique side of a monogon is a loop. -/
theorem side_zero_eq_side_one_monogon (i : Fin 1) : side i 0 = side i 1 := by
  simpa using (side_one_eq_rotate_zero i).symm

/-- The two sides of a digon meet at their middle vertex. -/
theorem side_zero_one_eq_side_one_zero_digon :
    side (0 : Fin 2) 1 = side (1 : Fin 2) 0 := by
  simpa using side_one_eq_rotate_zero (0 : Fin 2)

end PolygonCell

namespace PolygonGluing

universe u

/-- The disjoint union of a family of polygonal cells. -/
abbrev PreRealization (Face : Type u) (sideCount : Face → ℕ) : Type u :=
  Σ f, PolygonCell (sideCount f)

/-- A labelled side in a family of polygonal cells. -/
structure Side (Face : Type u) (sideCount : Face → ℕ) where
  /-- The `face` declaration. -/
  face : Face
  /-- The `index` declaration. -/
  index : Fin (sideCount face)

namespace Side

/-- A point on a labelled side, included in the disjoint union. -/
noncomputable def point {Face : Type u} {sideCount : Face → ℕ}
    (s : Side Face sideCount) (t : unitInterval) : PreRealization Face sideCount :=
  ⟨s.face, PolygonCell.side s.index t⟩

end Side

/-- The two affine self-homeomorphisms of the unit interval used to glue polygon sides. -/
inductive ParameterDirection where
  | same
  | opposite
deriving DecidableEq, Repr

namespace ParameterDirection

/-- The affine interval homeomorphism associated to a parameter direction. -/
def homeomorph : ParameterDirection → (unitInterval ≃ₜ unitInterval)
  | same => Homeomorph.refl unitInterval
  | opposite => unitInterval.symmHomeomorph

theorem homeomorph_same : homeomorph same = Homeomorph.refl unitInterval :=
  rfl

theorem homeomorph_opposite : homeomorph opposite = unitInterval.symmHomeomorph :=
  rfl

@[simp]
theorem homeomorph_same_apply (t : unitInterval) : homeomorph same t = t :=
  rfl

theorem homeomorph_opposite_apply (t : unitInterval) :
    homeomorph opposite t = unitInterval.symm t :=
  rfl

end ParameterDirection

/-- Instructions for identifying two polygon sides with an affine parameter map. -/
structure Identification (Face : Type u) (sideCount : Face → ℕ) where
  /-- The `source` declaration. -/
  source : Side Face sideCount
  /-- The `target` declaration. -/
  target : Side Face sideCount
  /-- The `direction` declaration. -/
  direction : ParameterDirection

namespace Identification

/-- The affine parameter homeomorphism of a side identification. -/
def parameter {Face : Type u} {sideCount : Face → ℕ}
    (identification : Identification Face sideCount) : unitInterval ≃ₜ unitInterval :=
  identification.direction.homeomorph

/-- Identify two sides with the same parameter direction. -/
def sameDirection {Face : Type u} {sideCount : Face → ℕ}
    (source target : Side Face sideCount) : Identification Face sideCount where
  source := source
  target := target
  direction := .same

/-- Identify two sides with the parameter direction reversed. -/
def oppositeDirection {Face : Type u} {sideCount : Face → ℕ}
    (source target : Side Face sideCount) : Identification Face sideCount where
  source := source
  target := target
  direction := .opposite

@[simp]
theorem parameter_sameDirection {Face : Type u} {sideCount : Face → ℕ}
    (source target : Side Face sideCount) :
    (sameDirection source target).parameter = Homeomorph.refl unitInterval :=
  rfl

@[simp]
theorem parameter_oppositeDirection {Face : Type u} {sideCount : Face → ℕ}
    (source target : Side Face sideCount) :
    (oppositeDirection source target).parameter = unitInterval.symmHomeomorph :=
  rfl

end Identification

/-- The elementary point identifications prescribed by a collection of side gluings. -/
inductive Generator {Face : Type u} {sideCount : Face → ℕ}
    (identifications : Set (Identification Face sideCount)) :
    PreRealization Face sideCount → PreRealization Face sideCount → Prop
  | glue (identification : Identification Face sideCount)
      (h : identification ∈ identifications) (t : unitInterval) :
      Generator identifications (identification.source.point t)
        (identification.target.point (identification.parameter t))

/-- The equivalence relation generated by the prescribed side identifications. -/
def setoid {Face : Type u} {sideCount : Face → ℕ}
    (identifications : Set (Identification Face sideCount)) :
    Setoid (PreRealization Face sideCount) :=
  Relation.EqvGen.setoid (Generator identifications)

@[simp]
theorem setoid_empty {Face : Type u} {sideCount : Face → ℕ} :
    setoid (∅ : Set (Identification Face sideCount)) = ⊥ := by
  apply Setoid.ext
  intro x y
  constructor
  · intro h
    change Relation.EqvGen (Generator ∅) x y at h
    induction h with
    | rel _ _ hxy =>
        cases hxy with
        | glue identification hi t => simp at hi
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h
    change x = y at h
    subst y
    exact Relation.EqvGen.refl x

theorem related_of_mem {Face : Type u} {sideCount : Face → ℕ}
    {identifications : Set (Identification Face sideCount)}
    (identification : Identification Face sideCount) (h : identification ∈ identifications)
    (t : unitInterval) :
    setoid identifications (identification.source.point t)
      (identification.target.point (identification.parameter t)) :=
  Relation.EqvGen.rel _ _ (Generator.glue identification h t)

/-- The quotient of the polygonal disjoint union by the generated side identifications. -/
abbrev Realization {Face : Type u} {sideCount : Face → ℕ}
    (identifications : Set (Identification Face sideCount)) : Type u :=
  Quotient (setoid identifications)

/-- The quotient map from the disjoint union to the glued realization. -/
def mk {Face : Type u} {sideCount : Face → ℕ}
    (identifications : Set (Identification Face sideCount)) :
    PreRealization Face sideCount → Realization identifications :=
  @Quotient.mk' _ (setoid identifications)

theorem continuous_mk {Face : Type u} {sideCount : Face → ℕ}
    (identifications : Set (Identification Face sideCount)) :
    Continuous (mk identifications) :=
  continuous_quotient_mk'

theorem isQuotientMap_mk {Face : Type u} {sideCount : Face → ℕ}
    (identifications : Set (Identification Face sideCount)) :
    _root_.Topology.IsQuotientMap (mk identifications) :=
  isQuotientMap_quotient_mk'

/-- A prescribed side gluing identifies the corresponding points in the quotient. -/
theorem mk_source_eq_mk_target {Face : Type u} {sideCount : Face → ℕ}
    {identifications : Set (Identification Face sideCount)}
    (identification : Identification Face sideCount) (h : identification ∈ identifications)
    (t : unitInterval) :
    mk identifications (identification.source.point t) =
      mk identifications (identification.target.point (identification.parameter t)) :=
  Quotient.sound (related_of_mem identification h t)

/-- A relation-preserving homeomorphism descends to polygonal realizations. -/
noncomputable def realizationCongr
    {Face₁ : Type u} {sideCount₁ : Face₁ → ℕ}
    {Face₂ : Type u} {sideCount₂ : Face₂ → ℕ}
    {identifications₁ : Set (Identification Face₁ sideCount₁)}
    {identifications₂ : Set (Identification Face₂ sideCount₂)}
    (e : PreRealization Face₁ sideCount₁ ≃ₜ PreRealization Face₂ sideCount₂)
    (h : ∀ x y, setoid identifications₁ x y ↔ setoid identifications₂ (e x) (e y)) :
    Realization identifications₁ ≃ₜ Realization identifications₂ :=
  Homeomorph.Quotient.congr e h

/-- Equal generated relations give homeomorphic realizations on a fixed pre-space. -/
noncomputable def realizationCongrRight
    {Face : Type u} {sideCount : Face → ℕ}
    {identifications₁ identifications₂ : Set (Identification Face sideCount)}
    (h : ∀ x y, setoid identifications₁ x y ↔ setoid identifications₂ x y) :
    Realization identifications₁ ≃ₜ Realization identifications₂ :=
  Homeomorph.Quotient.congrRight h

end PolygonGluing

end ClassificationOfSurfaces
end Topology
end LeanEval
