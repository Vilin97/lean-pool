/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantCoordinateHomotopy
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.NegativeReferenceCoordinateMap
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Local zero-free homotopies for the child-map family

The frozen child coordinate map depends continuously on the parent body and signed-interval
parameter.  Compactness of the order-complex realization upgrades this to a local uniform
estimate.  Consequently, outside the projected full-zero set, nearby frozen child maps are joined
by a zero-free straight-line homotopy.
-/

namespace NRR

open Geometry
open scoped BigOperators

namespace FoxNeuwirthOrderComplex
namespace EquivariantCoordinateHomotopy

variable {p : Nat}

/-- Joint child coordinate map, with the parent/interval parameter left variable. -/
noncomputable def childFamilyMap
    {K : Geometry.ConvexBody Plane} {A : Real}
    (hp : Nat.Prime p) (hA : 0 < A)
    (phi : NiceMV (BodySpace K (A / (p : Real)))) :
    C((BodySpace K A × SignedInterval) × Realization p, Fin p → Real) where
  toFun z := (orderComplexModel hp).childTestMap hA phi (((z.1.1, z.2), z.1.2))
  continuous_toFun := by
    exact ((orderComplexModel hp).continuous_childTestMap hA phi).comp
      (((continuous_fst.comp continuous_fst).prodMk continuous_snd).prodMk
        (continuous_snd.comp continuous_fst))

@[simp] theorem childFamilyMap_apply
    {K : Geometry.ConvexBody Plane} {A : Real}
    (hp : Nat.Prime p) (hA : 0 < A)
    (phi : NiceMV (BodySpace K (A / (p : Real))))
    (z : BodySpace K A × SignedInterval) (x : Realization p) :
    childFamilyMap hp hA phi (z, x) = childMap hp hA phi z x := rfl

/-- Uniform positive norm margin of one frozen zero-free child map. -/
theorem exists_childMap_norm_margin
    {K : Geometry.ConvexBody Plane} {A : Real}
    (hp : Nat.Prime p) (hA : 0 < A)
    (phi : NiceMV (BodySpace K (A / (p : Real))))
    (z : BodySpace K A × SignedInterval)
    (hz : z ∈ ((orderComplexModel hp).projectedAllChildrenZeroSet hA phi)ᶜ) :
    ∃ m : Real, 0 < m ∧ ∀ x : Realization p, m ≤ ‖childMap hp hA phi z x‖ :=
  RefinedAffineMap.exists_positive_norm_margin
    (childMap hp hA phi z) (childMap_zeroFree hp hA phi z hz)

/-- Nearby parameters give uniformly close frozen child maps. -/
theorem exists_uniform_childMap_neighborhood
    {K : Geometry.ConvexBody Plane} {A : Real}
    (hp : Nat.Prime p) (hA : 0 < A)
    (phi : NiceMV (BodySpace K (A / (p : Real))))
    (z : BodySpace K A × SignedInterval)
    {eps : Real} (heps : 0 < eps) :
    ∃ U : Set (BodySpace K A × SignedInterval),
      IsOpen U ∧ z ∈ U ∧
        ∀ w ∈ U, ∀ x : Realization p,
          ‖childMap hp hA phi w x - childMap hp hA phi z x‖ < eps := by
  let F := childFamilyMap hp hA phi
  have huc : UniformContinuous F :=
    CompactSpace.uniformContinuous_of_continuous F.continuous
  obtain ⟨delta, hdelta0, hdelta⟩ :=
    (Metric.uniformContinuous_iff.1 huc) eps heps
  let U : Set (BodySpace K A × SignedInterval) := Metric.ball z delta
  refine ⟨U, Metric.isOpen_ball, Metric.mem_ball_self hdelta0, ?_⟩
  intro w hw x
  have hprod : dist (w, x) (z, x) < delta := by
    simpa [Prod.dist_eq, U] using hw
  have hout := hdelta hprod
  change ‖(orderComplexModel hp).childTestMap hA phi ((w.1, x), w.2) -
      (orderComplexModel hp).childTestMap hA phi ((z.1, x), z.2)‖ < eps
  simpa [F, childFamilyMap, dist_eq_norm] using hout

/-- A vector segment stays nonzero when its moving endpoint remains closer than the norm margin. -/
theorem segment_ne_zero_of_norm_sub_lt
    {v w : Fin p → Real} {m : Real}
    (hm : m ≤ ‖v‖) (hclose : ‖w - v‖ < m)
    (t : Set.Icc (0 : Real) 1) :
    (1 - t.1) • v + t.1 • w ≠ 0 := by
  intro hzero
  have hbase : (1 - t.1) • v = -t.1 • w := by
    calc
      (1 - t.1) • v = (1 - t.1) • v + t.1 • w - t.1 • w := by module
      _ = -t.1 • w := by rw [hzero]; module
  have hrewrite : v = -t.1 • (w - v) := by
    calc
      v = (1 - t.1) • v + t.1 • v := by module
      _ = -t.1 • w + t.1 • v := by rw [hbase]
      _ = -t.1 • (w - v) := by module
  have ht0 : 0 ≤ t.1 := t.2.1
  have ht1 : t.1 ≤ 1 := t.2.2
  have hvle : ‖v‖ ≤ ‖w - v‖ := by
    calc
      ‖v‖ = ‖-t.1 • (w - v)‖ := congrArg norm hrewrite
      _ = t.1 * ‖w - v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg ht0]
      _ ≤ ‖w - v‖ := mul_le_of_le_one_left (norm_nonneg _) ht1
  exact (not_lt_of_ge (le_trans hm hvle)) hclose

/-- Outside the projected zero set, nearby frozen child maps are joined by a zero-free equivariant
straight-line homotopy. -/
theorem exists_local_zeroFreeHomotopy
    {K : Geometry.ConvexBody Plane} {A : Real}
    (hp : Nat.Prime p) (hA : 0 < A)
    (phi : NiceMV (BodySpace K (A / (p : Real))))
    (z : BodySpace K A × SignedInterval)
    (hz : z ∈ ((orderComplexModel hp).projectedAllChildrenZeroSet hA phi)ᶜ) :
    ∃ (U : Set (BodySpace K A × SignedInterval))
      (hUout : U ⊆ ((orderComplexModel hp).projectedAllChildrenZeroSet hA phi)ᶜ),
      IsOpen U ∧ z ∈ U ∧
      ∀ (w : BodySpace K A × SignedInterval) (hw : w ∈ U),
        Nonempty (ZeroFreeHomotopy hp
          (childZeroFreeMap hp hA phi z hz)
          (childZeroFreeMap hp hA phi w (hUout hw))) := by
  obtain ⟨m, hm0, hm⟩ := exists_childMap_norm_margin hp hA phi z hz
  obtain ⟨U0, hU0open, hzU0, hclose⟩ :=
    exists_uniform_childMap_neighborhood hp hA phi z (half_pos hm0)
  let carrier := (orderComplexModel hp).projectedAllChildrenZeroSet hA phi
  let U := U0 ∩ carrierᶜ
  have hUopen : IsOpen U := hU0open.inter
    (PrimeConfigurationModel.isClosed_projectedAllChildrenZeroSet
      (orderComplexModel hp) hA phi).isOpen_compl
  have hzU : z ∈ U := ⟨hzU0, hz⟩
  let hUout : U ⊆ carrierᶜ := Set.inter_subset_right
  refine ⟨U, hUout, hUopen, hzU, ?_⟩
  intro w hw
  let hwout : w ∈ carrierᶜ := hUout hw
  refine ⟨ZeroFreeHomotopy.segment
    (childZeroFreeMap hp hA phi z hz)
    (childZeroFreeMap hp hA phi w hwout) ?_⟩
  intro x t
  exact segment_ne_zero_of_norm_sub_lt (hm x)
    (lt_trans (hclose w hw.1 x) (by linarith)) t

end EquivariantCoordinateHomotopy
end FoxNeuwirthOrderComplex
end NRR
