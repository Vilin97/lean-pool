/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ReferenceAffineOrbitCount
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.OrderComplexRealization
import LeanPool.NandakumarRamanaRao.NRR.PrimeRefinement.ProjectedZeroSet

/-!
# Affine prism obstruction on the prime-orbit cycle

This module isolates the exact finite-dimensional content of Step S6.

For a coordinate-valued affine map on the Fox--Neuwirth order complex, the zero-sum part is
represented in fixed difference coordinates.  A zero of the difference map has a well-defined
common coordinate mean.  The obstruction counts, with the S4 cycle coefficients and the local
orientation index, only those zeros whose common mean is positive.

At the lower endpoint every child value is negative, so the positive count is zero.  At the upper
endpoint every child value is positive, so the positive count agrees with the ordinary deviation
zero count.  A finite affine prism supplies an incidence transgression between the positive-index
cochains at its endpoints; finite Stokes then proves equality of the orbit counts.

The final structure in this file records only the two transgression statements still required from
an equivariant affine approximation: local prisms away from the projected full-zero set and an
upper-end prism from the S5 reference map.  It does not contain a separator or assume local
constancy as a field.
-/

namespace NRR

open scoped BigOperators
open Geometry

variable {p : Nat}

namespace StandardSimplex

/-- Every barycentric point has at least one strictly positive coordinate. -/
theorem exists_pos {d : Nat} (w : StandardSimplex d) :
    ∃ i : Fin (d + 1), 0 < w i := by
  by_contra h
  push Not at h
  have hzero : ∀ i : Fin (d + 1), w i = 0 := by
    intro i
    exact le_antisymm (h i) (w.nonneg i)
  have : (∑ i, w i) = 0 := by simp [hzero]
  linarith [w.sum_eq_one]

end StandardSimplex

namespace FoxNeuwirthOrderComplex

/-- Coordinate-valued vertex data, before splitting into deviation and mean. -/
structure CoordinateAffineVertexMap (p : Nat) where
  /-- The coordinate vector assigned to each barred-permutation vertex. -/
  vertexValue : BarredPermutation p → Fin p → Real

namespace CoordinateAffineVertexMap

/-- Affine interpolation of the full coordinate vector on one maximal simplex. -/
noncomputable def value
    (F : CoordinateAffineVertexMap p)
    (s : Simplex p (p - 1))
    (w : StandardSimplex (p - 1)) : Fin p → Real :=
  fun i => ∑ j : Fin (p - 1 + 1), w j * F.vertexValue (s j) i


/-- Global piecewise-affine coordinate map on the barycentric realization. -/
noncomputable def globalValue
    (F : CoordinateAffineVertexMap p)
    (x : Realization p) : Fin p → Real :=
  fun i => ∑ c : BarredPermutation p, x c * F.vertexValue c i

/-- The global affine map agrees with the vertex data on realization vertices. -/
theorem globalValue_vertex
    (F : CoordinateAffineVertexMap p)
    (c : BarredPermutation p) :
    F.globalValue (Realization.vertex c) = F.vertexValue c := by
  funext i
  simp [globalValue, Realization.vertex_apply]

/-- The global affine map is continuous on the finite barycentric realization. -/
theorem continuous_globalValue
    (F : CoordinateAffineVertexMap p) :
    Continuous F.globalValue := by
  exact continuous_pi fun i =>
    continuous_finsetSum _ fun c _ =>
      ((continuous_apply c).comp continuous_subtype_val).mul continuous_const

/-- Fixed difference-coordinate representation of the zero-sum/deviation part. -/
noncomputable def deviation
    (hp : Nat.Prime p) (F : CoordinateAffineVertexMap p) :
    AffineVertexMap p (p - 1) where
  vertexValue c r :=
    F.vertexValue c (ReferenceAffineOrbitCount.coordinateLabel hp r) -
      F.vertexValue c (ReferenceAffineOrbitCount.lastLabel hp)

/-- Mean of the affine coordinate vector. -/
noncomputable def mean
    (p : Nat)
    (F : CoordinateAffineVertexMap p)
    (s : Simplex p (p - 1))
    (w : StandardSimplex (p - 1)) : Real :=
  coordinateMean p (F.value s w)

/-- Difference coordinates commute with affine interpolation. -/
theorem deviation_value_apply
    (hp : Nat.Prime p)
    (F : CoordinateAffineVertexMap p)
    (s : Simplex p (p - 1))
    (w : StandardSimplex (p - 1))
    (r : Fin (p - 1)) :
    (F.deviation hp).value s w r =
      F.value s w (ReferenceAffineOrbitCount.coordinateLabel hp r) -
        F.value s w (ReferenceAffineOrbitCount.lastLabel hp) := by
  simp only [deviation, AffineVertexMap.value, value, mul_sub, Finset.sum_sub_distrib]

/-- A positive zero is a relative-interior zero of the deviation map at which the common
coordinate mean is positive. -/
def HasPositiveInteriorZero
    (hp : Nat.Prime p)
    (F : CoordinateAffineVertexMap p)
    (s : Simplex p (p - 1)) : Prop :=
  ∃ w : StandardSimplex (p - 1),
    StandardSimplex.IsInterior w ∧
      (∀ r, (F.deviation hp).value s w r = 0) ∧
      0 < F.mean p s w

noncomputable instance hasPositiveInteriorZeroDecidable
    (hp : Nat.Prime p)
    (F : CoordinateAffineVertexMap p)
    (s : Simplex p (p - 1)) :
    Decidable (F.HasPositiveInteriorZero hp s) :=
  Classical.propDecidable _

/-- Signed local contribution of a positive deviation zero. -/
noncomputable def positiveLocalZeroIndex
    (hp : Nat.Prime p)
    (F : CoordinateAffineVertexMap p)
    (s : Simplex p (p - 1)) : ZMod p :=
  if F.HasPositiveInteriorZero hp s then
    AffineVertexMap.determinantIndex ((F.deviation hp).determinant s)
  else 0

/-- If every coordinate at every vertex is negative, every affine coordinate is negative. -/
theorem value_neg_of_vertex_neg
    (F : CoordinateAffineVertexMap p)
    (s : Simplex p (p - 1))
    (w : StandardSimplex (p - 1))
    (hneg : ∀ c i, F.vertexValue c i < 0)
    (i : Fin p) :
    F.value s w i < 0 := by
  obtain ⟨j, hj⟩ := w.exists_pos
  have hnonpos : ∀ k : Fin (p - 1 + 1), w k * F.vertexValue (s k) i ≤ 0 := by
    intro k
    exact mul_nonpos_of_nonneg_of_nonpos (w.nonneg k) (le_of_lt (hneg _ _))
  have hstrict : w j * F.vertexValue (s j) i < 0 :=
    mul_neg_of_pos_of_neg hj (hneg _ _)
  have hsumneg := Finset.sum_neg' (fun k _ => hnonpos k) ⟨j, Finset.mem_univ j, hstrict⟩
  simpa [value] using hsumneg

/-- If every coordinate at every vertex is positive, every affine coordinate is positive. -/
theorem value_pos_of_vertex_pos
    (F : CoordinateAffineVertexMap p)
    (s : Simplex p (p - 1))
    (w : StandardSimplex (p - 1))
    (hpos : ∀ c i, 0 < F.vertexValue c i)
    (i : Fin p) :
    0 < F.value s w i := by
  obtain ⟨j, hj⟩ := w.exists_pos
  have hnonneg : ∀ k : Fin (p - 1 + 1), 0 ≤ w k * F.vertexValue (s k) i := by
    intro k
    exact mul_nonneg (w.nonneg k) (le_of_lt (hpos _ _))
  have hstrict : 0 < w j * F.vertexValue (s j) i :=
    mul_pos hj (hpos _ _)
  have hsumpos := Finset.sum_pos' (fun k _ => hnonneg k) ⟨j, Finset.mem_univ j, hstrict⟩
  simpa [value] using hsumpos

/-- A coordinatewise-negative affine map has no positive zero. -/
theorem not_hasPositiveInteriorZero_of_vertex_neg
    (hp : Nat.Prime p)
    (F : CoordinateAffineVertexMap p)
    (hneg : ∀ c i, F.vertexValue c i < 0)
    (s : Simplex p (p - 1)) :
    ¬ F.HasPositiveInteriorZero hp s := by
  rintro ⟨w, hw, hdev, hmean⟩
  have hi : ∀ i : Fin p, F.value s w i < 0 := F.value_neg_of_vertex_neg s w hneg
  have hmeanneg : F.mean p s w < 0 := by
    unfold mean coordinateMean
    haveI : Nonempty (Fin p) := ⟨⟨0, hp.pos⟩⟩
    have hsumneg : (∑ i : Fin p, F.value s w i) < 0 :=
      Finset.sum_neg (fun i _ => hi i) Finset.univ_nonempty
    exact div_neg_of_neg_of_pos hsumneg (by exact_mod_cast hp.pos)
  linarith

/-- For a coordinatewise-positive affine map, every deviation zero has positive mean. -/
theorem hasPositiveInteriorZero_iff_of_vertex_pos
    (hp : Nat.Prime p)
    (F : CoordinateAffineVertexMap p)
    (hpos : ∀ c i, 0 < F.vertexValue c i)
    (s : Simplex p (p - 1)) :
    F.HasPositiveInteriorZero hp s ↔ (F.deviation hp).HasInteriorZero s := by
  constructor
  · rintro ⟨w, hw, hdev, hmean⟩
    exact ⟨w, hw, hdev⟩
  · rintro ⟨w, hw, hdev⟩
    refine ⟨w, hw, hdev, ?_⟩
    unfold mean coordinateMean
    have hi : ∀ i : Fin p, 0 < F.value s w i := F.value_pos_of_vertex_pos s w hpos
    haveI : Nonempty (Fin p) := ⟨⟨0, hp.pos⟩⟩
    have hsumpos : 0 < ∑ i : Fin p, F.value s w i :=
      Finset.sum_pos (fun i _ => hi i) Finset.univ_nonempty
    exact div_pos hsumpos (by exact_mod_cast hp.pos)

/-- Negative endpoint local indices vanish. -/
theorem positiveLocalZeroIndex_eq_zero_of_vertex_neg
    (hp : Nat.Prime p)
    (F : CoordinateAffineVertexMap p)
    (hneg : ∀ c i, F.vertexValue c i < 0)
    (s : Simplex p (p - 1)) :
    F.positiveLocalZeroIndex hp s = 0 := by
  simp [positiveLocalZeroIndex,
    F.not_hasPositiveInteriorZero_of_vertex_neg hp hneg s]

/-- At a positive endpoint the positive local index is the ordinary deviation local index. -/
theorem positiveLocalZeroIndex_eq_localZeroIndex_of_vertex_pos
    (hp : Nat.Prime p)
    (F : CoordinateAffineVertexMap p)
    (hpos : ∀ c i, 0 < F.vertexValue c i)
    (s : Simplex p (p - 1)) :
    F.positiveLocalZeroIndex hp s = (F.deviation hp).localZeroIndex s := by
  classical
  unfold positiveLocalZeroIndex AffineVertexMap.localZeroIndex
  exact if_congr (F.hasPositiveInteriorZero_iff_of_vertex_pos hp hpos s) rfl rfl

end CoordinateAffineVertexMap

namespace AffinePrismObstruction

open CoordinateAffineVertexMap

/-- Positive local-index cochain on the S4 top-orbit representatives. -/
noncomputable def positiveIndex
    (hp : Nat.Prime p)
    (F : CoordinateAffineVertexMap p) :
    PrimeOrbitCycle.TopOrbit hp → ZMod p :=
  fun q => F.positiveLocalZeroIndex hp (ReferenceAffineOrbitCount.topRepr hp q)

/-- An affine prism transgression is the finite Stokes datum produced by the signed zero set in
one parameter prism. -/
structure Transgression
    (hp : Nat.Prime p)
    (F₀ F₁ : CoordinateAffineVertexMap p) where
  /-- Facet-orbit indices whose coboundary records the change of positive index. -/
  facetIndex : PrimeOrbitCycle.FacetOrbit hp → ZMod p
  index_difference :
    positiveIndex hp F₁ - positiveIndex hp F₀ =
      (PrimeOrbitCycle.orbitCycle hp).coboundary facetIndex

namespace Transgression

/-- An affine prism preserves the positive orbit count. -/
theorem zeroCount_eq
    {hp : Nat.Prime p}
    {F₀ F₁ : CoordinateAffineVertexMap p}
    (H : Transgression hp F₀ F₁) :
    (PrimeOrbitCycle.orbitCycle hp).zeroCount (positiveIndex hp F₀) =
      (PrimeOrbitCycle.orbitCycle hp).zeroCount (positiveIndex hp F₁) := by
  exact (FiniteIncidenceCycle.IndexHomotopy.mk H.facetIndex H.index_difference).zeroCount_eq

end Transgression

/-- A complement-index family equipped with local affine prisms.  The local prism relation is
strictly stronger than the desired local constancy of the scalar count. -/
structure LocalPrismFamily
    {X : Type*} [TopologicalSpace X]
    (hp : Nat.Prime p) (carrier : Set X) where
  /-- The coordinate-valued vertex map assigned to each point outside the excluded carrier. -/
  map : ∀ z : X, z ∈ carrierᶜ → CoordinateAffineVertexMap p
  local_prism :
    ∀ (z : X) (hz : z ∈ carrierᶜ),
      ∃ (U : Set X) (hUout : U ⊆ carrierᶜ),
        IsOpen U ∧ z ∈ U ∧
          ∀ (w : X) (hw : w ∈ U),
            Nonempty (Transgression hp (map z hz) (map w (hUout hw)))

namespace LocalPrismFamily

/-- Scalar orbit obstruction value. -/
noncomputable def value
    {X : Type*} [TopologicalSpace X]
    {hp : Nat.Prime p} {carrier : Set X}
    (D : LocalPrismFamily hp carrier)
    (z : X) (hz : z ∈ carrierᶜ) : ZMod p :=
  (PrimeOrbitCycle.orbitCycle hp).zeroCount (positiveIndex hp (D.map z hz))

/-- Finite Stokes makes the scalar obstruction locally constant. -/
theorem locally_constant
    {X : Type*} [TopologicalSpace X]
    {hp : Nat.Prime p} {carrier : Set X}
    (D : LocalPrismFamily hp carrier)
    (z : X) (hz : z ∈ carrierᶜ) :
    ∃ (U : Set X) (hUout : U ⊆ carrierᶜ),
      IsOpen U ∧ z ∈ U ∧
        ∀ (w : X) (hw : w ∈ U),
          D.value w (hUout hw) = D.value z hz := by
  obtain ⟨U, hUout, hUopen, hzU, hprism⟩ := D.local_prism z hz
  refine ⟨U, hUout, hUopen, hzU, ?_⟩
  intro w hw
  obtain ⟨H⟩ := hprism w hw
  exact H.zeroCount_eq.symm

end LocalPrismFamily

end AffinePrismObstruction

/-- Vertex sampling of the actual child test map on the order-complex vertices. -/
noncomputable def childCoordinateVertexMap
    {K : Geometry.ConvexBody Plane} {A : Real}
    (hp : Nat.Prime p) (hA : 0 < A)
    (phi : NiceMV (BodySpace K (A / (p : Real))))
    (z : BodySpace K A × SignedInterval) : CoordinateAffineVertexMap p where
  vertexValue c i :=
    (orderComplexModel hp).childTestMap hA phi
      (((z.1, Realization.vertex c), z.2)) i

/-- Vertex values are strictly negative at the lower endpoint. -/
theorem childCoordinateVertexMap_left_neg
    {K : Geometry.ConvexBody Plane} {A : Real}
    (hp : Nat.Prime p) (hA : 0 < A)
    (phi : NiceMV (BodySpace K (A / (p : Real))))
    (C : BodySpace K A) :
    ∀ c i, (childCoordinateVertexMap hp hA phi (C, SignedInterval.left)).vertexValue c i < 0 := by
  intro c i
  exact phi.eval_left_neg _

/-- Vertex values are strictly positive at the upper endpoint. -/
theorem childCoordinateVertexMap_right_pos
    {K : Geometry.ConvexBody Plane} {A : Real}
    (hp : Nat.Prime p) (hA : 0 < A)
    (phi : NiceMV (BodySpace K (A / (p : Real))))
    (C : BodySpace K A) :
    ∀ c i, 0 < (childCoordinateVertexMap hp hA phi (C, SignedInterval.right)).vertexValue c i := by
  intro c i
  exact phi.eval_right_pos _

/-- The lower positive-index cochain is identically zero. -/
theorem childPositiveIndex_left_eq_zero
    {K : Geometry.ConvexBody Plane} {A : Real}
    (hp : Nat.Prime p) (hA : 0 < A)
    (phi : NiceMV (BodySpace K (A / (p : Real))))
    (C : BodySpace K A) :
    AffinePrismObstruction.positiveIndex hp
      (childCoordinateVertexMap hp hA phi (C, SignedInterval.left)) = 0 := by
  funext q
  exact CoordinateAffineVertexMap.positiveLocalZeroIndex_eq_zero_of_vertex_neg
    hp _ (childCoordinateVertexMap_left_neg hp hA phi C) _

/-- At the upper endpoint, the positive-index cochain is the ordinary deviation-index cochain. -/
theorem childPositiveIndex_right_eq_deviationIndex
    {K : Geometry.ConvexBody Plane} {A : Real}
    (hp : Nat.Prime p) (hA : 0 < A)
    (phi : NiceMV (BodySpace K (A / (p : Real))))
    (C : BodySpace K A) :
    AffinePrismObstruction.positiveIndex hp
      (childCoordinateVertexMap hp hA phi (C, SignedInterval.right)) =
      fun q =>
        ((childCoordinateVertexMap hp hA phi
          (C, SignedInterval.right)).deviation hp).localZeroIndex
            (ReferenceAffineOrbitCount.topRepr hp q) := by
  funext q
  exact CoordinateAffineVertexMap.positiveLocalZeroIndex_eq_localZeroIndex_of_vertex_pos
    hp _ (childCoordinateVertexMap_right_pos hp hA phi C) _

end FoxNeuwirthOrderComplex
end NRR
