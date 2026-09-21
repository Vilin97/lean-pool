/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Restrict
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LocalToCumulative

/-!
# Rebuilding a flag after deleting local mass

Nonzero cumulative supports are closed under transition.  Keeping the active
nodes and replacing their polytopes by these support hulls reconstructs a
flag decomposition, including visibility of every face.
-/

open scoped BigOperators

namespace EGZ.FlagDecompositionRaw

variable {p d : ℕ} [NeZero p] {F : ConvexFlag}

open Classical in
/-- The algebraic conditions needed to rebuild the support polytopes. -/
structure RebuildData (R : FpRepresentation p d F)
    (pieces : F.Node → FpCoord p d → ℕ) (f : FpCoord p d → ℕ) where
  odd : Odd p
  nonzero : ∃ x v, pieces x v ≠ 0
  local_supported : ∀ x v, pieces x v ≠ 0 → v ∈ R.space x
  retained_le : ∀ v, retainedWeight pieces v ≤ f v
  transition_hat_nonzero : ∀ {x y : F.Node} (h : x ≤ y)
    (z : IntCoord (F.rank x)), hat R pieces x z ≠ 0 →
      hat R pieces y ((F.transition h).integer z) ≠ 0
  hat_exists_local : ∀ (x : F.Node) (z : IntCoord (F.rank x)),
    hat R pieces x z ≠ 0 → ∃ y, ∃ h : y ≤ x,
      ∃ w : IntCoord (F.rank y), localLift R pieces y w ≠ 0 ∧
        (F.transition h).integer w = z

namespace RebuildData

variable {R : FpRepresentation p d F} {pieces : F.Node → FpCoord p d → ℕ}
    {f : FpCoord p d → ℕ} (D : RebuildData R pieces f)

include D

open Classical in
/-- A node is active when it has a nonzero local contribution below it. -/
def Active (_D : RebuildData R pieces f) (x : F.Node) : Prop :=
  ∃ y, y ≤ x ∧ ∃ v, pieces y v ≠ 0

open Classical in
theorem active_mono {x y : F.Node} (h : x ≤ y) (hx : D.Active x) :
    D.Active y := by
  obtain ⟨z, hzx, v, hv⟩ := hx
  exact ⟨z, hzx.trans h, v, hv⟩

open Classical in
theorem active_top : D.Active ⊤ := by
  obtain ⟨x, v, hv⟩ := D.nonzero
  exact ⟨x, le_top, v, hv⟩

open Classical in
abbrev ActiveNode := {x : F.Node // D.Active x}

open Classical in
noncomputable instance : Fintype D.ActiveNode := Subtype.fintype _

open Classical in
instance : SemilatticeSup D.ActiveNode :=
  Subtype.semilatticeSup fun _ _ hx _ ↦ D.active_mono le_sup_left hx

open Classical in
instance : OrderTop D.ActiveNode where
  top := ⟨⊤, D.active_top⟩
  le_top _ := le_top

open Classical in
theorem pieces_eq_zero_of_not_active {x : F.Node} (hx : ¬ D.Active x)
    (v : FpCoord p d) : pieces x v = 0 := by
  by_contra hv
  exact hx ⟨x, le_rfl, v, hv⟩

open Classical in
theorem cumulative_pos_of_active {x : F.Node} (hx : D.Active x) :
    ∃ v, cumulativeWeight pieces x v ≠ 0 := by
  obtain ⟨y, hyx, v, hv⟩ := hx
  refine ⟨v, ne_of_gt ((Nat.pos_of_ne_zero hv).trans_le ?_)⟩
  unfold cumulativeWeight
  simpa [hyx] using Finset.single_le_sum
    (f := fun y ↦ if y ≤ x then pieces y v else 0)
    (fun y _ ↦ Nat.zero_le _) (Finset.mem_univ y)

open Classical in
theorem hatSupport_nonempty {x : F.Node} (hx : D.Active x) :
    (hatSupport R pieces x).Nonempty := by
  obtain ⟨v, hv⟩ := D.cumulative_pos_of_active hx
  let z := FpCoord.centeredLift (R.map x v)
  refine ⟨z, (mem_hatSupport R pieces x z).mpr ?_⟩
  unfold hat
  rw [ite_eq_left (FpCoord.isCenteredLift_centeredLift D.odd _),
    FpCoord.mod_centeredLift]
  apply ne_of_gt ((Nat.pos_of_ne_zero hv).trans_le _)
  unfold affineFibreMass
  simpa using Finset.single_le_sum
    (f := fun w ↦ if R.map x w = R.map x v then cumulativeWeight pieces x w else 0)
    (fun w _ ↦ Nat.zero_le _) (Finset.mem_univ v)

open Classical in
theorem active_of_localLift_ne_zero {x : F.Node} {z : IntCoord (F.rank x)}
    (hz : localLift R pieces x z ≠ 0) : D.Active x := by
  by_contra hx
  apply hz
  unfold localLift affineFibreMass
  simp [D.pieces_eq_zero_of_not_active hx]

omit D in
open Classical in
theorem localLift_le_hat (x : F.Node) (z : IntCoord (F.rank x)) :
    localLift R pieces x z ≤ hat R pieces x z := by
  unfold localLift hat
  split_ifs
  · unfold affineFibreMass
    apply Finset.sum_le_sum
    intro v _
    split_ifs
    · unfold cumulativeWeight
      simpa using Finset.single_le_sum
        (f := fun y ↦ if y ≤ x then pieces y v else 0)
        (fun y _ ↦ Nat.zero_le _) (Finset.mem_univ x)
    · exact le_rfl
  · exact le_rfl

open Classical in
/-- The new polytope has exactly the surviving cumulative support as generators. -/
noncomputable def polytope (x : D.ActiveNode) : RationalPolytope (F.rank x.1) :=
  RationalPolytope.ofFinsetConvexHull ((hatSupport R pieces x.1).image IntCoord.real)
    ((D.hatSupport_nonempty x.2).image _)
    (by
      intro q hq
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hq
      intro i
      exact ⟨(z i : ℚ), by simp⟩)

open Classical in
@[simp]
theorem polytope_carrier (x : D.ActiveNode) :
    (D.polytope x).carrier =
      convexHull ℝ (IntCoord.real '' (↑(hatSupport R pieces x.1) :
        Set (IntCoord (F.rank x.1)))) := by
  simp only [polytope, RationalPolytope.ofFinsetConvexHull_carrier,
    Finset.coe_image]

open Classical in
theorem mem_polytope_of_localLift_ne_zero (x : D.ActiveNode)
    (z : IntCoord (F.rank x.1)) (hz : localLift R pieces x.1 z ≠ 0) :
    z.real ∈ (D.polytope x).carrier := by
  rw [D.polytope_carrier]
  apply subset_convexHull ℝ
  exact ⟨z, (mem_hatSupport R pieces x.1 z).mpr
    (ne_of_gt ((Nat.pos_of_ne_zero hz).trans_le (localLift_le_hat (R := R) (pieces := pieces) x.1 z))), rfl⟩

open Classical in
theorem transition_mem {x y : D.ActiveNode} (h : x ≤ y) {q : RealCoord (F.rank x.1)}
    (hq : q ∈ (D.polytope x).carrier) :
    (F.transition h).real q ∈ (D.polytope y).carrier := by
  rw [D.polytope_carrier] at hq
  apply convexHull_min (t := (F.transition h).real ⁻¹' (D.polytope y).carrier)
    ?_ ((D.polytope y).convex.affine_preimage _) hq
  rintro _ ⟨z, hz, rfl⟩
  change (F.transition h).real z.real ∈ (D.polytope y).carrier
  rw [(F.transition h).real_integer, D.polytope_carrier]
  apply subset_convexHull ℝ
  exact ⟨(F.transition h).integer z, (mem_hatSupport R pieces y.1 _).mpr
    (D.transition_hat_nonzero h z ((mem_hatSupport R pieces x.1 z).mp hz)), rfl⟩

open Classical in
/-- Retain active nodes and rebuild each support hull. -/
noncomputable abbrev flag : ConvexFlag where
  Node := D.ActiveNode
  rank x := F.rank x.1
  polytope := D.polytope
  lattice x := F.lattice x.1
  transition h := F.transition h
  transition_mem h := D.transition_mem h
  transition_lattice h := F.transition_lattice h
  transition_refl x := F.transition_refl x.1
  transition_trans hxy hyz := F.transition_trans hxy hyz

open Classical in
noncomputable def representation : FpRepresentation p d D.flag where
  space x := R.space x.1
  map x := R.map x.1
  space_mono h := R.space_mono h
  map_surjective x := R.map_surjective x.1
  compatible h := R.compatible h
  lattice_eq_standard x := R.lattice_eq_standard x.1

open Classical in
theorem sum_activeNode_eq (v : FpCoord p d) :
    ∑ x : D.ActiveNode, pieces x.1 v = ∑ x, pieces x v := by
  have h := Fintype.sum_subtype_add_sum_subtype D.Active (fun x ↦ pieces x v)
  have hz : (∑ x : {x // ¬ D.Active x}, pieces x.1 v) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact D.pieces_eq_zero_of_not_active x.2 v
  simpa only [hz, add_zero] using h

open Classical in
theorem cumulativeWeight_activeNode (x : D.ActiveNode) (v : FpCoord p d) :
    cumulativeWeight (F := D.flag) (fun y ↦ pieces y.1) x v =
      cumulativeWeight pieces x.1 v := by
  have h := Fintype.sum_subtype_add_sum_subtype D.Active
    (fun y ↦ if y ≤ x.1 then pieces y v else 0)
  have hz : (∑ y : {y // ¬ D.Active y}, if y.1 ≤ x.1 then pieces y.1 v else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro y _
    simp [D.pieces_eq_zero_of_not_active y.2 v]
  simpa only [cumulativeWeight, hz, add_zero, Subtype.coe_le_coe] using h

open Classical in
theorem hat_activeNode (x : D.ActiveNode) (z : IntCoord (F.rank x.1)) :
    hat D.representation (fun y ↦ pieces y.1) x z = hat R pieces x.1 z := by
  unfold hat
  have hw : cumulativeWeight (F := D.flag) (fun y ↦ pieces y.1) x =
      cumulativeWeight pieces x.1 := funext (D.cumulativeWeight_activeNode x)
  rw [hw]
  rfl

open Classical in
/-- Every face of a rebuilt support hull contains a projection of a surviving
local generator, so it remains visible to the proper-point set. -/
theorem faces_visible (x : D.ActiveNode) (Γ : (D.polytope x).Face) :
    VisibleFace D.representation (fun y ↦ pieces y.1) x Γ := by
  obtain ⟨q, hq⟩ := Γ.generatorFinset_nonempty
  have hq' := Finset.mem_filter.mp hq
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq'.1
  have hz' := (mem_hatSupport R pieces x.1 z).mp hz
  obtain ⟨y, hyx, w, hw, hwz⟩ := D.hat_exists_local x.1 z hz'
  let y' : D.ActiveNode := ⟨y, D.active_of_localLift_ne_zero hw⟩
  let r : D.flag.Point := ⟨y', w.real, D.mem_polytope_of_localLift_ne_zero y' w hw⟩
  refine ⟨r, ConvexFlag.subset_convexHull D.flag _ ?_, hyx, ?_⟩
  · exact ⟨w, rfl, hw⟩
  · change (F.transition hyx).real w.real ∈ Γ.carrier
    rw [(F.transition hyx).real_integer, hwz]
    exact hq'.2

open Classical in
/-- Rebuild a decomposition with precisely the surviving mass at active
nodes.  The constructor proves all flag and visibility invariants. -/
noncomputable abbrev decomposition : FlagDecomposition p d f where
  flag := D.flag
  representation := D.representation
  localWeight x := pieces x.1
  local_supported x := D.local_supported x.1
  retained_le v := by
    change (∑ x : D.ActiveNode, pieces x.1 v) ≤ f v
    rw [D.sum_activeNode_eq]
    exact D.retained_le v
  liftedSupport x := hatSupport R pieces x.1
  liftedSupport_spec x z := by
    rw [D.hat_activeNode]
    exact mem_hatSupport R pieces x.1 z
  liftedSupport_nonempty x := D.hatSupport_nonempty x.2
  polytope_eq_liftedSupport x := D.polytope_carrier x
  faces_visible := D.faces_visible

open Classical in
@[simp]
theorem decomposition_cumulativeWeight (x : D.ActiveNode) :
    D.decomposition.cumulativeWeight x = cumulativeWeight pieces x.1 :=
  funext (D.cumulativeWeight_activeNode x)

open Classical in
@[simp]
theorem decomposition_hat (x : D.ActiveNode) :
    D.decomposition.hat x = hat R pieces x.1 := funext (D.hat_activeNode x)

open Classical in
@[simp]
theorem decomposition_retainedWeight :
    D.decomposition.retainedWeight = retainedWeight pieces :=
  funext (D.sum_activeNode_eq)

open Classical in
theorem card_decomposition_le : Fintype.card D.decomposition.flag.Node ≤ Fintype.card F.Node :=
  Fintype.card_subtype_le _

end RebuildData

end EGZ.FlagDecompositionRaw
