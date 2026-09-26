/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LiftedMass
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.PruningStability

/-!
# Mass transport at surviving nodes

An integral coordinate map compatible with the cumulative ambient atoms
transports centered lifts exactly.  A stable node map additionally bounds
the loss at the node by the loss of the entire decomposition. These data
compose, so the same estimates apply along a surviving lineage.
-/

@[expose] public section

open scoped BigOperators

namespace EGZ.FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}

open Classical in
/-- A compatible integral affine node map whose cumulative weight does not increase. -/
structure NodeMassMap (Φ Ψ : FlagDecomposition p d f)
    (x : Φ.flag.Node) (y : Ψ.flag.Node) where
  /-- The integral affine map from the new node's coordinates to the original node's
  coordinates. -/
  coord : IntegralAffineMap (Ψ.flag.rank y) (Φ.flag.rank x)
  polytope_mem : Set.MapsTo coord.real (Ψ.flag.polytope y).carrier
    (Φ.flag.polytope x).carrier
  cumulative_le : Ψ.cumulativeWeight y ≤ Φ.cumulativeWeight x
  map_eq : ∀ v, Ψ.cumulativeWeight y v ≠ 0 →
    coord.modp p (Ψ.representation.map y v) = Φ.representation.map x v

namespace NodeMassMap

variable {Φ Ψ Ω : FlagDecomposition p d f}
    {x : Φ.flag.Node} {y : Ψ.flag.Node} {z : Ω.flag.Node}

open Classical in
/-- The identity map on a node and its cumulative weight. -/
def refl (Φ : FlagDecomposition p d f) (x : Φ.flag.Node) : NodeMassMap Φ Φ x x where
  coord := IntegralAffineMap.id _
  polytope_mem := fun _ h ↦ h
  cumulative_le := le_rfl
  map_eq := fun _ _ ↦ rfl

open Classical in
/-- Compose compatible coordinate and cumulative-weight maps between three nodes. -/
def comp (M : NodeMassMap Φ Ψ x y) (N : NodeMassMap Ψ Ω y z) :
    NodeMassMap Φ Ω x z where
  coord := M.coord.comp N.coord
  polytope_mem := fun _ h ↦ M.polytope_mem (N.polytope_mem h)
  cumulative_le := N.cumulative_le.trans M.cumulative_le
  map_eq v hv := by
    change M.coord.modp p (N.coord.modp p (Ω.representation.map z v)) = _
    rw [N.map_eq v hv]
    exact M.map_eq v (fun h ↦ hv (Nat.eq_zero_of_le_zero (h ▸ N.cumulative_le v)))

open Classical in
theorem centeredLift_eq (M : NodeMassMap Φ Ψ x y) (hp : Odd p)
    (v : FpCoord p d) (hv : Ψ.cumulativeWeight y v ≠ 0) :
    M.coord.integer (FpCoord.centeredLift (Ψ.representation.map y v)) =
      FpCoord.centeredLift (Φ.representation.map x v) := by
  let q := FpCoord.centeredLift (Ψ.representation.map y v)
  have hq : q ∈ Ψ.liftedSupport y := by
    apply (Ψ.liftedSupport_spec y q).mpr
    exact (Ψ.originalWeights.hat_ne_zero_iff y q).mpr
      ⟨FpCoord.isCenteredLift_centeredLift hp _, v,
        (FpCoord.mod_centeredLift _).symm, hv⟩
  have hmem : q.real ∈ (Ψ.flag.polytope y).carrier := by
    rw [Ψ.polytope_eq_liftedSupport]
    exact subset_convexHull ℝ _ ⟨q, hq, rfl⟩
  have hc : IsCenteredLift p (M.coord.integer q) := by
    apply Φ.isCenteredLift_of_mem_polytope x
    rw [← M.coord.real_integer]
    exact M.polytope_mem hmem
  have hm : (M.coord.integer q).mod p = Φ.representation.map x v := by
    rw [← M.coord.mod_integer, show q.mod p = Ψ.representation.map y v from
      FpCoord.mod_centeredLift _, M.map_eq v hv]
  rw [← hm, FpCoord.centeredLift_mod hc]

open Classical in
theorem real_centeredLift_eq (M : NodeMassMap Φ Ψ x y) (hp : Odd p)
    (v : FpCoord p d) (hv : Ψ.cumulativeWeight y v ≠ 0) :
    M.coord.real (FpCoord.centeredLift (Ψ.representation.map y v)).real =
      (FpCoord.centeredLift (Φ.representation.map x v)).real := by
  rw [M.coord.real_integer, M.centeredLift_eq hp v hv]

open Classical in
theorem liftedMassOn_preimage (M : NodeMassMap Φ Ψ x y) (hp : Odd p)
    (S : Set (RealCoord (Φ.flag.rank x))) :
    Ψ.liftedMassOn y (M.coord.real ⁻¹' S) =
      natMassOn (Ψ.cumulativeWeight y)
        {v | (FpCoord.centeredLift (Φ.representation.map x v)).real ∈ S} := by
  rw [Ψ.liftedMassOn_eq_natMassOn hp]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : Ψ.cumulativeWeight y v = 0
  · simp only [hv, ite_self]
  · simp only [Set.mem_ofPred_eq, Set.mem_preimage, M.real_centeredLift_eq hp v hv]

open Classical in
theorem liftedMassOn_preimage_le (M : NodeMassMap Φ Ψ x y) (hp : Odd p)
    (S : Set (RealCoord (Φ.flag.rank x))) :
    Ψ.liftedMassOn y (M.coord.real ⁻¹' S) ≤ Φ.liftedMassOn x S := by
  rw [M.liftedMassOn_preimage hp, Φ.liftedMassOn_eq_natMassOn hp]
  exact natMassOn_mono_weight M.cumulative_le _

open Classical in
theorem liftedMassOn_loss_le (M : NodeMassMap Φ Ψ x y) (hp : Odd p)
    (S : Set (RealCoord (Φ.flag.rank x))) :
    (Φ.liftedMassOn x S : ℝ) - Ψ.liftedMassOn y (M.coord.real ⁻¹' S) ≤
      (natMass (Φ.cumulativeWeight x) : ℝ) - natMass (Ψ.cumulativeWeight y) := by
  rw [M.liftedMassOn_preimage hp, Φ.liftedMassOn_eq_natMassOn hp]
  exact natMassOn_loss_le_real M.cumulative_le _

end NodeMassMap

open Classical in
/-- A node mass map whose mass loss is bounded by the decomposition's total retained-mass
loss. -/
structure StableNodeMap (Φ Ψ : FlagDecomposition p d f)
    (x : Φ.flag.Node) (y : Ψ.flag.Node) extends NodeMassMap Φ Ψ x y where
  mass_loss_le : (natMass (Φ.cumulativeWeight x) : ℝ) -
    natMass (Ψ.cumulativeWeight y) ≤ (Φ.retainedMass : ℝ) - Ψ.retainedMass

namespace StableNodeMap

variable {Φ Ψ Ω : FlagDecomposition p d f}
    {x : Φ.flag.Node} {y : Ψ.flag.Node} {z : Ω.flag.Node}

open Classical in
/-- The identity stable node map, with zero mass loss. -/
def refl (Φ : FlagDecomposition p d f) (x : Φ.flag.Node) : StableNodeMap Φ Φ x x where
  toNodeMassMap := NodeMassMap.refl Φ x
  mass_loss_le := by simp

open Classical in
/-- Compose stable node maps, adding their bounds on mass loss. -/
def comp (M : StableNodeMap Φ Ψ x y) (N : StableNodeMap Ψ Ω y z) :
    StableNodeMap Φ Ω x z where
  toNodeMassMap := M.toNodeMassMap.comp N.toNodeMassMap
  mass_loss_le := by linarith [M.mass_loss_le, N.mass_loss_le]

open Classical in
theorem liftedMassOn_loss_le (M : StableNodeMap Φ Ψ x y) (hp : Odd p)
    (S : Set (RealCoord (Φ.flag.rank x))) :
    (Φ.liftedMassOn x S : ℝ) - Ψ.liftedMassOn y (M.coord.real ⁻¹' S) ≤
      (Φ.retainedMass : ℝ) - Ψ.retainedMass :=
  (M.toNodeMassMap.liftedMassOn_loss_le hp S).trans M.mass_loss_le

end StableNodeMap
end EGZ.FlagDecomposition
