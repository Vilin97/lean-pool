/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.ScalarExtension
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LatticeCoordinates
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.MinimalRepresentation
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Reduction

/-!
# Lifted mass in new lattice coordinates

An injective modular chart and centered new support coordinates identify the
old and new centered fibres on every ambient atom carrying cumulative mass.
Summing that pointwise identification proves exact transport for every weight
bounded by the cumulative weight, including the local summand.
-/

open scoped BigOperators

namespace EGZ

namespace FlagDecompositionRaw

open Classical in
/-- The centered lift of a weight through one coordinate map. -/
noncomputable def centeredFibreMass {p d n : ℕ} [NeZero p]
    (w : FpCoord p d → ℕ) (φ : FpCoord p d → FpCoord p n)
    (q : IntCoord n) : ℕ := by
  classical
  exact if IsCenteredLift p q then affineFibreMass w φ (q.mod p) else 0

open Classical in
theorem centeredFibreMass_eq_sum {p d n : ℕ} [NeZero p]
    (w : FpCoord p d → ℕ) (φ : FpCoord p d → FpCoord p n) (q : IntCoord n) :
    centeredFibreMass w φ q =
      ∑ v, if IsCenteredLift p q ∧ φ v = q.mod p then w v else 0 := by
  classical
  by_cases hc : IsCenteredLift p q <;>
    simp only [centeredFibreMass, hc, ite_true, ite_false, true_and, false_and,
      affineFibreMass, Finset.sum_const_zero]

end FlagDecompositionRaw

namespace IntegerLatticeChart

open Classical in
/-- Express a finite-field representation map in the chart coordinates. -/
noncomputable def rechartMap {p d n : ℕ} [Fact p.Prime]
    {S : Finset (IntCoord n)} (C : IntegerLatticeChart S)
    (φ : FpCoord p d →ᵃ[ZMod p] FpCoord p n) :
    FpCoord p d →ᵃ[ZMod p] FpCoord p C.rank :=
  (affineLeftInverse ((IntegralAffineMap.ofIntAffineMap C.map).modp p)).comp φ

end IntegerLatticeChart

namespace FlagDecomposition

variable {p d : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}

omit [Fact p.Prime] in
open Classical in
/-- Every ambient atom carrying cumulative mass lifts into the stored support. -/
theorem centeredLift_mem_liftedSupport (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.flag.Node) {v : FpCoord p d} (hv : Φ.cumulativeWeight x v ≠ 0) :
    FpCoord.centeredLift (Φ.representation.map x v) ∈ Φ.liftedSupport x := by
  classical
  rw [Φ.liftedSupport_spec]
  unfold FlagDecompositionRaw.hat
  rw [ite_eq_left (FpCoord.isCenteredLift_centeredLift hp _), FpCoord.mod_centeredLift]
  have hle : Φ.cumulativeWeight x v ≤
      FlagDecompositionRaw.affineFibreMass (Φ.cumulativeWeight x)
        (Φ.representation.map x) (Φ.representation.map x v) := by
    simpa [FlagDecompositionRaw.affineFibreMass] using
      Finset.single_le_sum
        (f := fun w ↦ if Φ.representation.map x w = Φ.representation.map x v
          then Φ.cumulativeWeight x w else 0)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ v)
  exact ne_of_gt ((Nat.pos_of_ne_zero hv).trans_le hle)

open Classical in
/-- On a supported atom the new finite-field coordinate is the reduction of
the inverse chart coordinate of its old centered lift. -/
theorem rechartMap_eq_coordinates_mod (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.flag.Node) (C : IntegerLatticeChart (Φ.liftedSupport x))
    (hmod : Function.Injective ((IntegralAffineMap.ofIntAffineMap C.map).modp p))
    {v : FpCoord p d} (hv : Φ.cumulativeWeight x v ≠ 0) :
    C.rechartMap (Φ.representation.map x) v =
      (C.coordinates (FpCoord.centeredLift (Φ.representation.map x v))).mod p := by
  have hz := Φ.centeredLift_mem_liftedSupport hp x hv
  have hcoord := congrArg (IntCoord.mod p) (C.map_coordinates_of_mem hz)
  have hchart : (IntegralAffineMap.ofIntAffineMap C.map).modp p
      ((C.coordinates (FpCoord.centeredLift (Φ.representation.map x v))).mod p) =
      Φ.representation.map x v := by
    rw [IntegralAffineMap.mod_integer]
    exact hcoord.trans (FpCoord.mod_centeredLift _)
  change affineLeftInverse ((IntegralAffineMap.ofIntAffineMap C.map).modp p)
    (Φ.representation.map x v) = _
  conv_lhs => rw [← hchart]
  exact affineLeftInverse_apply _ hmod _

open Classical in
/-- Centered old and new fibre conditions agree on every supported atom,
including when the displayed test coordinate is outside a centered box. -/
theorem rechart_centered_fibre_iff (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.flag.Node) (C : IntegerLatticeChart (Φ.liftedSupport x))
    (hmod : Function.Injective ((IntegralAffineMap.ofIntAffineMap C.map).modp p))
    (hcenter : ∀ q ∈ C.coordinateSupport, IsCenteredLift p q)
    {v : FpCoord p d} (hv : Φ.cumulativeWeight x v ≠ 0) (q : IntCoord C.rank) :
    (IsCenteredLift p q ∧ C.rechartMap (Φ.representation.map x) v = q.mod p) ↔
      (IsCenteredLift p (C.map q) ∧ Φ.representation.map x v = (C.map q).mod p) := by
  let z := FpCoord.centeredLift (Φ.representation.map x v)
  have hz : z ∈ Φ.liftedSupport x := Φ.centeredLift_mem_liftedSupport hp x hv
  have hzc : IsCenteredLift p z := FpCoord.isCenteredLift_centeredLift hp _
  have hc : IsCenteredLift p (C.coordinates z) :=
    hcenter _ (C.coordinates_mem_coordinateSupport hz)
  have hmap : C.map (C.coordinates z) = z := C.map_coordinates_of_mem hz
  have hnew : C.rechartMap (Φ.representation.map x) v = (C.coordinates z).mod p :=
    Φ.rechartMap_eq_coordinates_mod hp x C hmod hv
  have hzmod : z.mod p = Φ.representation.map x v := FpCoord.mod_centeredLift _
  constructor
  · rintro ⟨hq, hqmod⟩
    have heq : q = C.coordinates z := hq.eq_of_mod_eq hc (hqmod.symm.trans hnew)
    rw [heq, hmap]
    exact ⟨hzc, hzmod.symm⟩
  · rintro ⟨hq, hqmod⟩
    have heq : C.map q = z := hq.eq_of_mod_eq hzc (hqmod.symm.trans hzmod.symm)
    have hqcoord : q = C.coordinates z := C.injective (heq.trans hmap.symm)
    rw [hqcoord]
    exact ⟨hc, hnew⟩

open Classical in
/-- Exact transport of any centered lifted weight dominated by the old
cumulative weight. The equality holds at every integer coordinate. -/
theorem centeredFibreMass_rechart (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.flag.Node) (C : IntegerLatticeChart (Φ.liftedSupport x))
    (hmod : Function.Injective ((IntegralAffineMap.ofIntAffineMap C.map).modp p))
    (hcenter : ∀ q ∈ C.coordinateSupport, IsCenteredLift p q)
    (w : FpCoord p d → ℕ) (hw : w ≤ Φ.cumulativeWeight x) (q : IntCoord C.rank) :
    FlagDecompositionRaw.centeredFibreMass w (C.rechartMap (Φ.representation.map x)) q =
      FlagDecompositionRaw.centeredFibreMass w (Φ.representation.map x) (C.map q) := by
  classical
  rw [FlagDecompositionRaw.centeredFibreMass_eq_sum,
    FlagDecompositionRaw.centeredFibreMass_eq_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : w v = 0
  · simp [hv]
  · have hvold : Φ.cumulativeWeight x v ≠ 0 :=
      ne_of_gt ((Nat.pos_of_ne_zero hv).trans_le (hw v))
    have heq := Φ.rechart_centered_fibre_iff hp x C hmod hcenter hvold q
    simp only [heq]

open Classical in
/-- Cumulative lifted mass is unchanged after expressing the support in its
own integer lattice coordinates. -/
theorem hat_rechart (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.flag.Node) (C : IntegerLatticeChart (Φ.liftedSupport x))
    (hmod : Function.Injective ((IntegralAffineMap.ofIntAffineMap C.map).modp p))
    (hcenter : ∀ q ∈ C.coordinateSupport, IsCenteredLift p q) (q : IntCoord C.rank) :
    FlagDecompositionRaw.centeredFibreMass (Φ.cumulativeWeight x)
      (C.rechartMap (Φ.representation.map x)) q = Φ.hat x (C.map q) :=
  Φ.centeredFibreMass_rechart hp x C hmod hcenter (Φ.cumulativeWeight x) le_rfl q

open Classical in
/-- The same exact transport holds for the local lift defining proper-point
generators, not just for cumulative mass. -/
theorem localLift_rechart (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.flag.Node) (C : IntegerLatticeChart (Φ.liftedSupport x))
    (hmod : Function.Injective ((IntegralAffineMap.ofIntAffineMap C.map).modp p))
    (hcenter : ∀ q ∈ C.coordinateSupport, IsCenteredLift p q) (q : IntCoord C.rank) :
    FlagDecompositionRaw.centeredFibreMass (Φ.localWeight x)
      (C.rechartMap (Φ.representation.map x)) q = Φ.localLift x (C.map q) :=
  Φ.centeredFibreMass_rechart hp x C hmod hcenter (Φ.localWeight x)
    (Φ.localWeight_le_cumulativeWeight x) q

open Classical in
/-- The support transported by the chart is exactly the nonzero support of
the recharted cumulative lift. -/
theorem coordinateSupport_spec_rechart (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.flag.Node) (C : IntegerLatticeChart (Φ.liftedSupport x))
    (hmod : Function.Injective ((IntegralAffineMap.ofIntAffineMap C.map).modp p))
    (hcenter : ∀ q ∈ C.coordinateSupport, IsCenteredLift p q) (q : IntCoord C.rank) :
    q ∈ C.coordinateSupport ↔ FlagDecompositionRaw.centeredFibreMass
      (Φ.cumulativeWeight x) (C.rechartMap (Φ.representation.map x)) q ≠ 0 := by
  rw [Φ.hat_rechart hp x C hmod hcenter, C.mem_coordinateSupport, Φ.liftedSupport_spec]
  rfl

end FlagDecomposition
end EGZ
