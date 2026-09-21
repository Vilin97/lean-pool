/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Rebuild
import LeanPool.ErdosGinzburgZiv.EGZ.Convex.Faces

/-!
# Decompositions on a prescribed support diagram

An exact nonempty cumulative support at every node permits packaging a
decomposition on the given flag itself. Integer transitions preserving these
supports imply face visibility, so visibility is not an extra input.
-/

open scoped BigOperators

namespace EGZ

namespace RationalPolytope.Face

variable {n : ℕ} {P : RationalPolytope n}

open Classical in
/-- Every nonempty face of a finite hull contains one of its generators,
even when that finite hull differs from the polytope's stored presentation. -/
theorem exists_mem_of_eq_convexHull (Γ : P.Face) (S : Finset (RealCoord n))
    (hP : P.carrier = convexHull ℝ (S : Set (RealCoord n))) :
    ∃ q ∈ S, q ∈ Γ.carrier := by
  obtain ⟨ξ, c, hle, hcarrier⟩ := Γ.is_exposed
  have hleS : ∀ q ∈ S, ξ q ≤ c := by
    intro q hq
    apply hle q
    rw [hP]
    exact subset_convexHull ℝ _ hq
  have hface : Γ.carrier = convexHull ℝ
      (↑(S.filter (fun q ↦ ξ q = c)) : Set (RealCoord n)) := by
    rw [hcarrier, hP]
    exact RationalPolytope.convexHull_supportingLevel_eq S ξ c hleS
  have hnonempty : (S.filter (fun q ↦ ξ q = c)).Nonempty := by
    by_contra h
    have heq := Finset.not_nonempty_iff_eq_empty.mp h
    have hne := Γ.nonempty
    rw [hface, heq] at hne
    simp at hne
  obtain ⟨q, hq⟩ := hnonempty
  refine ⟨q, (Finset.mem_filter.mp hq).1, ?_⟩
  rw [hface]
  exact subset_convexHull ℝ _ hq

end RationalPolytope.Face

namespace FlagDecompositionRaw

variable {p d : ℕ} [NeZero p] {F : ConvexFlag}

open Classical in
/-- A local lifted fibre contributes to its cumulative lifted fibre. -/
theorem localLift_le_hat (R : FpRepresentation p d F)
    (pieces : F.Node → FpCoord p d → ℕ) (x : F.Node)
    (q : IntCoord (F.rank x)) : localLift R pieces x q ≤ hat R pieces x q := by
  unfold localLift hat
  split_ifs
  · unfold affineFibreMass
    apply Finset.sum_le_sum
    intro v _
    split_ifs
    · unfold cumulativeWeight
      simpa using Finset.single_le_sum
        (f := fun y ↦ if y ≤ x then pieces y v else 0)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ x)
    · exact le_rfl
  · exact le_rfl

open Classical in
/-- Exact support data on the nodes of a prescribed flag. -/
structure SupportData (R : FpRepresentation p d F)
    (pieces : F.Node → FpCoord p d → ℕ) where
  /-- The finite set of integral coordinates where the node's cumulative centered lift is
  nonzero. -/
  support : (x : F.Node) → Finset (IntCoord (F.rank x))
  support_spec : ∀ x q, q ∈ support x ↔ hat R pieces x q ≠ 0
  support_nonempty : ∀ x, (support x).Nonempty
  polytope_eq : ∀ x, (F.polytope x).carrier =
    convexHull ℝ (IntCoord.real '' (↑(support x) : Set (IntCoord (F.rank x))))
  transition_support : ∀ {x y : F.Node} (h : x ≤ y)
    (q : IntCoord (F.rank x)), q ∈ support x →
      (F.transition h).integer q ∈ support y
  local_supported : ∀ x v, pieces x v ≠ 0 → v ∈ R.space x

namespace SupportData

variable {R : FpRepresentation p d F} {pieces : F.Node → FpCoord p d → ℕ}
    (D : SupportData R pieces)

include D

open Classical in
theorem support_centered (x : F.Node) (q : IntCoord (F.rank x))
    (hq : q ∈ D.support x) : IsCenteredLift p q := by
  have hne := (D.support_spec x q).mp hq
  by_contra hc
  exact hne (ite_eq_right hc)

open Classical in
theorem mem_support_of_localLift_ne_zero (x : F.Node) (q : IntCoord (F.rank x))
    (hq : localLift R pieces x q ≠ 0) : q ∈ D.support x := by
  apply (D.support_spec x q).mpr
  exact ne_of_gt ((Nat.pos_of_ne_zero hq).trans_le
    (localLift_le_hat R pieces x q))

open Classical in
theorem mem_polytope_of_localLift_ne_zero (x : F.Node) (q : IntCoord (F.rank x))
    (hq : localLift R pieces x q ≠ 0) : q.real ∈ (F.polytope x).carrier := by
  rw [D.polytope_eq]
  apply subset_convexHull ℝ
  exact ⟨q, D.mem_support_of_localLift_ne_zero x q hq, rfl⟩

open Classical in
theorem transition_centered_of_localLift_ne_zero {x y : F.Node} (h : x ≤ y)
    (q : IntCoord (F.rank x)) (hq : localLift R pieces x q ≠ 0) :
    IsCenteredLift p ((F.transition h).integer q) :=
  D.support_centered y _
    (D.transition_support h q (D.mem_support_of_localLift_ne_zero x q hq))

open Classical in
/-- A cumulative support atom has a local antecedent with exact integer
transition coordinates. -/
theorem exists_localLift_of_hat_ne_zero (hp : Odd p) (x : F.Node)
    (q : IntCoord (F.rank x)) (hq : hat R pieces x q ≠ 0) :
    ∃ (y : F.Node) (h : y ≤ x) (z : IntCoord (F.rank y)),
      localLift R pieces y z ≠ 0 ∧ (F.transition h).integer z = q := by
  have heq := hat_eq_localIntegerMassBelow hp R pieces D.local_supported x q
    (fun _ h z hz ↦ D.transition_centered_of_localLift_ne_zero h z hz)
  rw [heq] at hq
  obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
  by_cases hyx : y ≤ x
  · rw [dite_eq_left hyx] at hy
    obtain ⟨z, _, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
    by_cases heq : (F.transition hyx).integer z = q
    · exact ⟨y, hyx, z, by simpa only [ite_eq_left heq] using hz, heq⟩
    · exact (hz (ite_eq_right heq)).elim
  · exact (hy (dite_eq_right hyx)).elim

open Classical in
/-- Support generation and transition compatibility imply that every face
contains a proper point. -/
theorem faces_visible (hp : Odd p) (x : F.Node) (Γ : (F.polytope x).Face) :
    VisibleFace R pieces x Γ := by
  obtain ⟨q, hq, hface⟩ := Γ.exists_mem_of_eq_convexHull
    ((D.support x).image IntCoord.real)
    (by simpa only [Finset.coe_image] using D.polytope_eq x)
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨y, hyx, w, hw, hwz⟩ := D.exists_localLift_of_hat_ne_zero hp x z
    ((D.support_spec x z).mp hz)
  let r : F.Point := ⟨y, w.real, D.mem_polytope_of_localLift_ne_zero y w hw⟩
  refine ⟨r, ConvexFlag.subset_convexHull F _ ?_, hyx, ?_⟩
  · exact ⟨w, rfl, hw⟩
  · change (F.transition hyx).real w.real ∈ Γ.carrier
    rw [(F.transition hyx).real_integer, hwz]
    exact hface

open Classical in
/-- Package a decomposition while retaining the prescribed flag, its nodes,
its representation, and all local weights definitionally. -/
noncomputable abbrev decomposition (hp : Odd p) (f : FpCoord p d → ℕ)
    (hretained : ∀ v, retainedWeight pieces v ≤ f v) : FlagDecomposition p d f where
  flag := F
  representation := R
  localWeight := pieces
  local_supported := D.local_supported
  retained_le := hretained
  liftedSupport := D.support
  liftedSupport_spec := D.support_spec
  liftedSupport_nonempty := D.support_nonempty
  polytope_eq_liftedSupport := D.polytope_eq
  faces_visible := D.faces_visible hp

open Classical in
@[simp]
theorem decomposition_retainedWeight (hp : Odd p) (f : FpCoord p d → ℕ)
    (hretained : ∀ v, retainedWeight pieces v ≤ f v) :
    (D.decomposition hp f hretained).retainedWeight = retainedWeight pieces := rfl

open Classical in
@[simp]
theorem decomposition_cumulativeWeight (hp : Odd p) (f : FpCoord p d → ℕ)
    (hretained : ∀ v, retainedWeight pieces v ≤ f v) (x : F.Node) :
    (D.decomposition hp f hretained).cumulativeWeight x = cumulativeWeight pieces x := rfl

open Classical in
@[simp]
theorem decomposition_hat (hp : Odd p) (f : FpCoord p d → ℕ)
    (hretained : ∀ v, retainedWeight pieces v ≤ f v) (x : F.Node) :
    (D.decomposition hp f hretained).hat x = hat R pieces x := rfl

open Classical in
@[simp]
theorem decomposition_localLift (hp : Odd p) (f : FpCoord p d → ℕ)
    (hretained : ∀ v, retainedWeight pieces v ≤ f v) (x : F.Node) :
    (D.decomposition hp f hretained).localLift x = localLift R pieces x := rfl

end SupportData
end FlagDecompositionRaw
end EGZ
