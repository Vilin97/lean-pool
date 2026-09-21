/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.ConvexFlag.Centerpoint
import LeanPool.ErdosGinzburgZiv.EGZ.Consistency.PropositionSevenOne
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LiftedMass
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.GapCleanup
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Completeness

/-!
# From the flag centerpoint to a cumulative fibre

Local ambient atoms are used as a labelled weighted family. Repeated
generating points retain their separate masses; the centerpoint theorem
does not require the family to be injective. Compatibility and centered
integer transitions identify its upper masses with cumulative lifted mass.
-/

open scoped BigOperators

namespace EGZ

namespace ConvexFlag

open Classical in
theorem flagCenterpoint_fintype {F : ConvexFlag} (Ω : F.ProperPointSet)
    {I : Type*} [Fintype I] (points : I → F.Point)
    (hproper : ∀ i, points i ∈ Ω) (hintegral : ∀ i, (points i).IsIntegral)
    (weight : I → ℝ) (hweight : ∀ i, 0 ≤ weight i) (htotal : 0 < ∑ i, weight i) :
    ∃ q, q ∈ Ω ∧ q.IsIntegral ∧
      ∀ (ξ : F.LinearFunction) (hq : ξ.EvaluableAt q),
        (∑ i, weight i) / (hellyConstant Ω : ℝ) ≤
          ∑ i, if ∃ hi : ξ.EvaluableAt (points i),
            ξ.eval q hq ≤ ξ.eval (points i) hi then weight i else 0 := by
  let e := (Fintype.equivFin I).symm
  obtain ⟨q, hq, hint, h⟩ := flagCenterpoint_family Ω (fun i ↦ points (e i))
    (fun i ↦ hproper (e i)) (fun i ↦ hintegral (e i)) (fun i ↦ weight (e i))
    (fun i ↦ hweight (e i)) (by simpa only [e.sum_comp] using htotal)
  refine ⟨q, hq, hint, fun ξ hq ↦ ?_⟩
  have hh := h ξ hq
  simp only [upperWeight, Finset.sum_filter] at hh
  rw [e.sum_comp weight] at hh
  have he := e.sum_comp (fun i : I ↦ if ∃ hi : ξ.EvaluableAt (points i),
    ξ.eval q hq ≤ ξ.eval (points i) hi then weight i else 0)
  exact hh.trans_eq he

end ConvexFlag

namespace FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f)

open Classical in
/-- The nonzero local ambient atoms, with node labels retained. -/
abbrev LocalAtom := {a : Φ.flag.Node × FpCoord p d // Φ.localWeight a.1 a.2 ≠ 0}

open Classical in
theorem localLift_centeredLift_ne_zero (hp : Odd p) (x : Φ.flag.Node)
    (v : FpCoord p d) (hv : Φ.localWeight x v ≠ 0) :
    Φ.localLift x (FpCoord.centeredLift (Φ.representation.map x v)) ≠ 0 := by
  have hc := FpCoord.isCenteredLift_centeredLift hp (Φ.representation.map x v)
  change (if IsCenteredLift p _ then FlagDecompositionRaw.affineFibreMass
    (Φ.localWeight x) (Φ.representation.map x) _ else 0) ≠ 0
  rw [ite_eq_left hc, FpCoord.mod_centeredLift]
  apply ne_of_gt ((Nat.pos_of_ne_zero hv).trans_le ?_)
  unfold FlagDecompositionRaw.affineFibreMass
  simpa only [ite_true] using Finset.single_le_sum
    (f := fun w ↦ if Φ.representation.map x w = Φ.representation.map x v
      then Φ.localWeight x w else 0)
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ v)

open Classical in
/-- The flag point associated with a local atom through its centered integral lift. -/
def localAtomPoint (hp : Odd p) (a : Φ.LocalAtom) : Φ.flag.Point where
  base := a.1.1
  val := (FpCoord.centeredLift (Φ.representation.map a.1.1 a.1.2)).real
  val_mem := Φ.mem_polytope_of_localLift_ne_zero _ _
    (Φ.localLift_centeredLift_ne_zero hp _ _ a.2)

open Classical in
theorem localAtomPoint_proper (hp : Odd p) (a : Φ.LocalAtom) :
    Φ.localAtomPoint hp a ∈ Φ.properPoints :=
  ConvexFlag.subset_convexHull Φ.flag Φ.omegaZero
    ⟨_, rfl, Φ.localLift_centeredLift_ne_zero hp _ _ a.2⟩

open Classical in
theorem localAtomPoint_integral (hp : Odd p) (a : Φ.LocalAtom) :
    (Φ.localAtomPoint hp a).IsIntegral :=
  (Φ.representation.lattice_eq_standard _ _).mpr ⟨_, rfl⟩

open Classical in
theorem sum_localAtom_weight : (∑ a : Φ.LocalAtom, Φ.localWeight a.1.1 a.1.2) = Φ.retainedMass := by
  have hz : (∑ a : {a : Φ.flag.Node × FpCoord p d // ¬ Φ.localWeight a.1 a.2 ≠ 0},
      Φ.localWeight a.1.1 a.1.2) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact not_ne_iff.mp a.2
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun a : Φ.flag.Node × FpCoord p d ↦ Φ.localWeight a.1 a.2 ≠ 0)
    (fun a ↦ Φ.localWeight a.1 a.2)
  rw [hz, add_zero, Fintype.sum_prod_type] at hs
  rw [hs]
  unfold retainedMass retainedWeight FlagDecompositionRaw.retainedWeight natMass
  exact Finset.sum_comm

open Classical in
theorem localAtomPoint_coord (hp : Odd p) (a : Φ.LocalAtom) {x : Φ.flag.Node}
    (h : a.1.1 ≤ x) :
    (Φ.localAtomPoint hp a).coord h =
      (FpCoord.centeredLift (Φ.representation.map x a.1.2)).real := by
  let z := FpCoord.centeredLift (Φ.representation.map a.1.1 a.1.2)
  have hc := Φ.isCenteredLift_transition_of_localLift h z
    (Φ.localLift_centeredLift_ne_zero hp _ _ a.2)
  have hm : ((Φ.flag.transition h).integer z).mod p = Φ.representation.map x a.1.2 := by
    rw [← (Φ.flag.transition h).mod_integer, FpCoord.mod_centeredLift]
    exact (Φ.representation.compatible h (Φ.local_supported _ _ a.2)).symm
  change (Φ.flag.transition h).real z.real = _
  rw [(Φ.flag.transition h).real_integer, ← FpCoord.centeredLift_mod hc, hm]

open Classical in
/-- Grouping local ambient atoms below a node gives exactly its cumulative
lifted mass on any set of real coordinates. -/
theorem sum_localAtom_on (hp : Odd p) (x : Φ.flag.Node)
    (S : Set (RealCoord (Φ.flag.rank x))) :
    (∑ a : Φ.LocalAtom, if a.1.1 ≤ x ∧
      (FpCoord.centeredLift (Φ.representation.map x a.1.2)).real ∈ S
      then Φ.localWeight a.1.1 a.1.2 else 0) = Φ.liftedMassOn x S := by
  let w (a : Φ.flag.Node × FpCoord p d) :=
    if a.1 ≤ x ∧ (FpCoord.centeredLift (Φ.representation.map x a.2)).real ∈ S
      then Φ.localWeight a.1 a.2 else 0
  have hz : (∑ a : {a : Φ.flag.Node × FpCoord p d // ¬ Φ.localWeight a.1 a.2 ≠ 0},
      w a) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    simp only [w, not_ne_iff.mp a.2, ite_self]
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun a : Φ.flag.Node × FpCoord p d ↦ Φ.localWeight a.1 a.2 ≠ 0) w
  rw [hz, add_zero] at hs
  change (∑ a : Φ.LocalAtom, w a) = _
  rw [hs, Fintype.sum_prod_type, Φ.liftedMassOn_eq_natMassOn hp]
  unfold natMassOn cumulativeWeight FlagDecompositionRaw.cumulativeWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : (FpCoord.centeredLift (Φ.representation.map x v)).real ∈ S
  · simp only [w, hv, and_true, Set.mem_ofPred_eq, ite_true]
  · simp only [w, hv, and_false, Set.mem_ofPred_eq, ite_false, Finset.sum_const_zero]

open Classical in
/-- The flag centerpoint has an integral base coordinate, and every closed
halfspace through it carries at least retained mass divided by the flag's
Helly constant in the cumulative lift at that base. -/
theorem exists_cumulative_centerpoint_helly (hp : Odd p) :
    ∃ q : Φ.flag.Point, q ∈ Φ.omega ∧ q.IsIntegral ∧
      ∀ ξ : RealCoord (Φ.flag.rank q.base) →ᵃ[ℝ] ℝ,
        (Φ.retainedMass : ℝ) / (ConvexFlag.hellyConstant Φ.properPoints : ℝ) ≤
          (Φ.liftedMassOn q.base {z | ξ q.val ≤ ξ z} : ℝ) := by
  have hsum : (∑ a : Φ.LocalAtom, (Φ.localWeight a.1.1 a.1.2 : ℝ)) = Φ.retainedMass := by
    exact_mod_cast Φ.sum_localAtom_weight
  have hpos : 0 < ∑ a : Φ.LocalAtom, (Φ.localWeight a.1.1 a.1.2 : ℝ) := by
    rw [hsum]
    exact_mod_cast Φ.retainedMass_pos hp
  obtain ⟨q, hq, hint, hcentral⟩ := ConvexFlag.flagCenterpoint_fintype Φ.properPoints
    (Φ.localAtomPoint hp) (Φ.localAtomPoint_proper hp) (Φ.localAtomPoint_integral hp)
    (fun a ↦ (Φ.localWeight a.1.1 a.1.2 : ℝ)) (fun _ ↦ Nat.cast_nonneg _) hpos
  refine ⟨q, hq, hint, fun ξ ↦ ?_⟩
  have h := hcentral ⟨q.base, ξ⟩ le_rfl
  rw [hsum] at h
  have hpred (a : Φ.LocalAtom) :
      (∃ ha : a.1.1 ≤ q.base, ξ q.val ≤ ξ ((Φ.localAtomPoint hp a).coord ha)) ↔
        a.1.1 ≤ q.base ∧
          ξ q.val ≤ ξ (FpCoord.centeredLift (Φ.representation.map q.base a.1.2)).real := by
    constructor
    · rintro ⟨ha, hh⟩
      exact ⟨ha, by simpa only [Φ.localAtomPoint_coord hp a ha] using hh⟩
    · rintro ⟨ha, hh⟩
      exact ⟨ha, by simpa only [Φ.localAtomPoint_coord hp a ha] using hh⟩
  change (Φ.retainedMass : ℝ) / _ ≤ ∑ a : Φ.LocalAtom,
    if ∃ ha : a.1.1 ≤ q.base, ξ (q.coord le_rfl) ≤ ξ ((Φ.localAtomPoint hp a).coord ha)
      then (Φ.localWeight a.1.1 a.1.2 : ℝ) else 0 at h
  simp only [ConvexFlag.Point.coord_base, hpred] at h
  have hmass := Φ.sum_localAtom_on hp q.base {z | ξ q.val ≤ ξ z}
  have hmassR : (∑ a : Φ.LocalAtom, if a.1.1 ≤ q.base ∧
      ξ q.val ≤ ξ (FpCoord.centeredLift (Φ.representation.map q.base a.1.2)).real
      then (Φ.localWeight a.1.1 a.1.2 : ℝ) else 0) =
      (Φ.liftedMassOn q.base {z | ξ q.val ≤ ξ z} : ℝ) := by
    exact_mod_cast hmass
  exact h.trans_eq hmassR

open Classical in
/-- Proposition 7.1 converts the cumulative centerpoint bound to the hollow
constant of the original finite-field space. -/
theorem exists_cumulative_centerpoint (hp : p.Prime) (hodd : Odd p) :
    ∃ q : Φ.flag.Point, q ∈ Φ.omega ∧ q.IsIntegral ∧
      ∀ ξ : RealCoord (Φ.flag.rank q.base) →ᵃ[ℝ] ℝ,
        (Φ.retainedMass : ℝ) / (hollowConstant p d : ℝ) ≤
          (Φ.liftedMassOn q.base {z | ξ q.val ≤ ξ z} : ℝ) := by
  obtain ⟨q, hq, hint, hc⟩ := Φ.exists_cumulative_centerpoint_helly hodd
  have hH : 0 < ConvexFlag.hellyConstant Φ.properPoints :=
    ConvexFlag.hellyConstant_pos hq hint
  refine ⟨q, hq, hint, fun ξ ↦ ?_⟩
  apply le_trans _ (hc ξ)
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by exact_mod_cast hH)
    (by exact_mod_cast Φ.propositionSevenOne hp)

open Classical in
/-- The constant zero functional detects the entire cumulative mass,
including when the base lattice has dimension zero. -/
theorem cumulativeMass_lower_of_halfspace_lower (hodd : Odd p)
    (q : Φ.flag.Point) {a : ℝ}
    (h : ∀ ξ : RealCoord (Φ.flag.rank q.base) →ᵃ[ℝ] ℝ,
      a ≤ (Φ.liftedMassOn q.base {z | ξ q.val ≤ ξ z} : ℝ)) :
    a ≤ natMass (Φ.cumulativeWeight q.base) := by
  have hz := h (AffineMap.const ℝ _ (0 : ℝ))
  simp only [AffineMap.const_apply, le_refl, Set.ofPred_true] at hz
  rw [Φ.liftedMassOn_eq_natMassOn hodd] at hz
  simpa only [natMassOn, Set.mem_ofPred_eq, Set.mem_univ, ite_true, natMass] using hz

open Classical in
theorem isLargeElement_of_halfspace_lower (hodd : Odd p)
    (q : Φ.flag.Point) {ε : ℝ}
    (h : ∀ ξ : RealCoord (Φ.flag.rank q.base) →ᵃ[ℝ] ℝ,
      ε * (Φ.retainedMass : ℝ) ≤ (Φ.liftedMassOn q.base {z | ξ q.val ≤ ξ z} : ℝ)) :
    Φ.IsLargeElement ε q.base := by
  rw [Φ.isLargeElement_iff_natMass hodd]
  exact Φ.cumulativeMass_lower_of_halfspace_lower hodd q h

open Classical in
/-- The cumulative centerpoint lies at a node large at inverse-hollow scale. -/
theorem exists_cumulative_centerpoint_large (hp : p.Prime) (hodd : Odd p) :
    ∃ q : Φ.flag.Point, q ∈ Φ.omega ∧ q.IsIntegral ∧
      Φ.IsLargeElement (hollowConstant p d : ℝ)⁻¹ q.base ∧
      ∀ ξ : RealCoord (Φ.flag.rank q.base) →ᵃ[ℝ] ℝ,
        (Φ.retainedMass : ℝ) / (hollowConstant p d : ℝ) ≤
          (Φ.liftedMassOn q.base {z | ξ q.val ≤ ξ z} : ℝ) := by
  obtain ⟨q, hq, hint, hc⟩ := Φ.exists_cumulative_centerpoint hp hodd
  refine ⟨q, hq, hint, ?_, hc⟩
  apply Φ.isLargeElement_of_halfspace_lower hodd q
  intro ξ
  simpa only [div_eq_mul_inv, mul_comm] using hc ξ

end FlagDecomposition
end EGZ
