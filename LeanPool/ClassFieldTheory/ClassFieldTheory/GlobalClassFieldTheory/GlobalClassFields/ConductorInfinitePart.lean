/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorLocalComparison
/-!
# Removing one real place from a defining modulus

This file gives the one-place archimedean step toward the full conductor.
Removing the positivity condition at a real place preserves the defining
property exactly when the whole one-place idèle-class image is already
contained in the target subgroup.
-/

open scoped NumberField
noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- Erasing a selected real place can only decrease a full modulus. -/
theorem eraseRealPlace_le
    (m : RayClass.Modulus K) (v : RayClass.RealPlace K) :
    m.eraseRealPlace v ≤ m :=
  ⟨le_rfl, Finset.erase_subset v m.infinitePart⟩

open scoped Classical in
/-- If a real place is not selected by a modulus, its whole one-place
idèle-class image lies in the corresponding ray congruence subgroup. -/
theorem infinitePlaceIdeleClass_range_le_congruenceSubgroup_of_not_mem
    (m : RayClass.Modulus K) (v : RayClass.RealPlace K)
    (hv : v ∉ m.infinitePart) :
    (IdeleGroup.infinitePlaceIdeleClass v.1).range ≤
      m.congruenceSubgroup := by
  rintro _ ⟨x, rfl⟩
  rw [RayClass.Modulus.congruenceSubgroup]
  refine ⟨IdeleGroup.infinitePlaceIdele v.1 x, ?_, rfl⟩
  apply Subgroup.mem_sup_left
  rw [RayClass.Modulus.mem_ideleCongruenceSubgroup_iff]
  refine ⟨?_, ?_⟩
  · rw [RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff]
    intro w hw
    have hwv : w ≠ v := by
      intro hwv
      subst w
      exact hv hw
    have hwv' : w.1 ≠ v.1 := by
      intro h
      exact hwv (Subtype.ext h)
    change
      IdeleGroup.infiniteComponent w.1
          (IdeleGroup.infinitePlaceIdele v.1 x) ∈
        RayClass.infinitePositiveSubgroup w.1
    rw [IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne
      v.1 w.1 x hwv']
    exact Subgroup.one_mem _
  · rw [RayClass.mem_finiteCongruenceSubgroup_iff]
    intro w
    change
      IdeleGroup.finiteComponent w
          (IdeleGroup.infinitePlaceIdele v.1 x) ∈
        RayClass.localHigherUnitGroup w (m.finitePart w)
    rw [IdeleGroup.infinitePlaceIdele_finiteComponent]
    exact Subgroup.one_mem _

open scoped Classical in
private theorem eraseRealPlace_isDefiningModulus_of_range_le
    (H : Subgroup (IdeleClassGroup K))
    (m : RayClass.Modulus K)
    (hm : IsDefiningModulus H m)
    (v : RayClass.RealPlace K)
    (hvH : (IdeleGroup.infinitePlaceIdeleClass v.1).range ≤ H) :
    IsDefiningModulus H (m.eraseRealPlace v) := by
  let m' : RayClass.Modulus K := m.eraseRealPlace v
  change IsDefiningModulus H m'
  let q : IdeleGroup K →* IdeleClassGroup K :=
    QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
  rw [IsDefiningModulus, RayClass.Modulus.congruenceSubgroup,
    Subgroup.map_le_iff_le_comap]
  apply sup_le
  · intro a ha
    have ha' :=
      (RayClass.Modulus.mem_ideleCongruenceSubgroup_iff m' a).1 ha
    let s : IdeleGroup K :=
      IdeleGroup.infinitePlaceIdele v.1
        (IdeleGroup.infiniteComponent v.1 a)
    let b : IdeleGroup K := a * s⁻¹
    have hsH : q s ∈ H := by
      change
        IdeleGroup.infinitePlaceIdeleClass v.1
            (IdeleGroup.infiniteComponent v.1 a) ∈ H
      apply hvH
      exact ⟨IdeleGroup.infiniteComponent v.1 a, rfl⟩
    have hbCong : b ∈ m.ideleCongruenceSubgroup := by
      rw [RayClass.Modulus.mem_ideleCongruenceSubgroup_iff]
      refine ⟨?_, ?_⟩
      · rw [RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff]
        intro w hw
        by_cases hwv : w = v
        · subst w
          change
            IdeleGroup.infiniteComponent v.1 b ∈
              RayClass.infinitePositiveSubgroup v.1
          dsimp only [b]
          rw [map_mul, map_inv]
          dsimp only [s]
          rw [IdeleGroup.infinitePlaceIdele_infiniteComponent_same,
            mul_inv_cancel]
          exact Subgroup.one_mem _
        · have hw' : w ∈ m'.infinitePart := by
            change w ∈ m.infinitePart.erase v
            exact Finset.mem_erase.mpr ⟨hwv, hw⟩
          have haw :=
            (RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff
              m' a.1).1 ha'.1 w hw'
          have hwv' : w.1 ≠ v.1 := by
            intro h
            exact hwv (Subtype.ext h)
          change
            IdeleGroup.infiniteComponent w.1 b ∈
              RayClass.infinitePositiveSubgroup w.1
          dsimp only [b]
          rw [map_mul, map_inv]
          dsimp only [s]
          rw [IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne
              v.1 w.1 _ hwv',
            inv_one, mul_one]
          exact haw
      · rw [RayClass.mem_finiteCongruenceSubgroup_iff]
        intro w
        have haw :
            a.2 w ∈ RayClass.localHigherUnitGroup w (m.finitePart w) := by
          simpa [m'] using ha'.2 w
        change
          IdeleGroup.finiteComponent w b ∈
            RayClass.localHigherUnitGroup w (m.finitePart w)
        dsimp only [b]
        rw [map_mul, map_inv]
        dsimp only [s]
        rw [IdeleGroup.infinitePlaceIdele_finiteComponent,
          inv_one, mul_one, IdeleGroup.finiteComponent_apply]
        exact haw
    have hbH : q b ∈ H := by
      apply hm
      rw [RayClass.Modulus.congruenceSubgroup]
      exact ⟨b, Subgroup.mem_sup_left hbCong, rfl⟩
    have hab : a = b * s := by
      dsimp [b]
      group
    change q a ∈ H
    rw [hab, map_mul]
    exact H.mul_mem hbH hsH
  · intro a ha
    change q a ∈ H
    have hqa : q a = 1 :=
      (QuotientGroup.eq_one_iff a).2 ha
    rw [hqa]
    exact H.one_mem

open scoped Classical in
/-- Removing the positivity condition at one real place preserves the
defining-modulus property exactly when the whole one-place idèle-class
image is already contained in the target subgroup. -/
theorem eraseRealPlace_isDefiningModulus_iff
    (H : Subgroup (IdeleClassGroup K))
    (m : RayClass.Modulus K)
    (v : RayClass.RealPlace K) :
    IsDefiningModulus H (m.eraseRealPlace v) ↔
      IsDefiningModulus H m ∧
        (IdeleGroup.infinitePlaceIdeleClass v.1).range ≤ H := by
  constructor
  · intro hm'
    refine ⟨?_, ?_⟩
    · exact
        (RayClass.Modulus.congruenceSubgroup_antitone
          (eraseRealPlace_le m v)).trans hm'
    · exact
        (infinitePlaceIdeleClass_range_le_congruenceSubgroup_of_not_mem
          (m.eraseRealPlace v) v (by simp)).trans hm'
  · rintro ⟨hm, hvH⟩
    exact eraseRealPlace_isDefiningModulus_of_range_le H m hm v hvH

open scoped Classical in
/-- Erasing finitely many real places preserves the defining-modulus
property when every corresponding one-place idèle-class image is contained
in the target subgroup. -/
theorem eraseRealPlaces_isDefiningModulus_of_ranges_le
    (H : Subgroup (IdeleClassGroup K))
    (m : RayClass.Modulus K)
    (hm : IsDefiningModulus H m)
    (s : Finset (RayClass.RealPlace K))
    (hs : ∀ v ∈ s,
      (IdeleGroup.infinitePlaceIdeleClass v.1).range ≤ H) :
    IsDefiningModulus H (m.eraseRealPlaces s) := by
  classical
  revert hs
  induction s using Finset.induction_on with
  | empty =>
      intro _hs
      simpa only [RayClass.Modulus.eraseRealPlaces_empty] using hm
  | @insert v s _ ih =>
      intro hs
      rw [RayClass.Modulus.eraseRealPlaces_insert]
      exact
        (eraseRealPlace_isDefiningModulus_iff H
          (m.eraseRealPlaces s) v).2
          ⟨ih (fun w hw => hs w (Finset.mem_insert_of_mem hw)),
            hs v (Finset.mem_insert_self v s)⟩

namespace ConductorialSubgroup

open scoped Classical in
/-- The real places whose one-place idèle-class image is not contained in
the target subgroup. -/
noncomputable def fullConductorInfinitePart
    (H : ConductorialSubgroup K) : Finset (RayClass.RealPlace K) :=
  (Finset.univ : Finset (RayClass.RealPlace K)).filter fun v =>
    ¬ (IdeleGroup.infinitePlaceIdeleClass v.1).range ≤ H.1

open scoped Classical in
/-- Membership in the infinite part of the full conductor is the failure of
the corresponding one-place idèle-class image to lie in the target subgroup. -/
@[simp]
theorem mem_fullConductorInfinitePart_iff
    (H : ConductorialSubgroup K) (v : RayClass.RealPlace K) :
    v ∈ H.fullConductorInfinitePart ↔
      ¬ (IdeleGroup.infinitePlaceIdeleClass v.1).range ≤ H.1 := by
  simp only [fullConductorInfinitePart, Finset.mem_filter,
    Finset.mem_univ, true_and]

open scoped Classical in
/-- Every defining modulus contains the infinite part of the full conductor. -/
theorem fullConductorInfinitePart_subset_of_isDefiningModulus
    (H : ConductorialSubgroup K) {m : RayClass.Modulus K}
    (hm : IsDefiningModulus H.1 m) :
    H.fullConductorInfinitePart ⊆ m.infinitePart := by
  intro v hv
  have hvNot := (H.mem_fullConductorInfinitePart_iff v).1 hv
  by_contra hvm
  exact hvNot
    ((infinitePlaceIdeleClass_range_le_congruenceSubgroup_of_not_mem
      m v hvm).trans hm)

open scoped Classical in
/-- The full conductor, with the narrow finite conductor as finite part and
exactly the required real places as infinite part. -/
noncomputable def fullConductor
    (H : ConductorialSubgroup K) : RayClass.Modulus K where
  finitePart := H.narrowFiniteConductor
  infinitePart := H.fullConductorInfinitePart

open scoped Classical in
/-- The full conductor is itself a defining modulus. -/
theorem fullConductor_isDefiningModulus
    (H : ConductorialSubgroup K) :
    IsDefiningModulus H.1 H.fullConductor := by
  obtain ⟨m, hm, hfinite⟩ :=
    H.exists_definingModulus_finitePart_eq_narrowFiniteConductor
  let s : Finset (RayClass.RealPlace K) :=
    m.infinitePart \ H.fullConductorInfinitePart
  have hs : ∀ v ∈ s,
      (IdeleGroup.infinitePlaceIdeleClass v.1).range ≤ H.1 := by
    intro v hv
    have hvNot : v ∉ H.fullConductorInfinitePart :=
      (Finset.mem_sdiff.mp hv).2
    by_contra hvRange
    exact hvNot (H.mem_fullConductorInfinitePart_iff v |>.2 hvRange)
  have hmErase :
      IsDefiningModulus H.1 (m.eraseRealPlaces s) :=
    eraseRealPlaces_isDefiningModulus_of_ranges_le H.1 m hm s hs
  have hsubset : H.fullConductorInfinitePart ⊆ m.infinitePart :=
    H.fullConductorInfinitePart_subset_of_isDefiningModulus hm
  have hmod : m.eraseRealPlaces s = H.fullConductor := by
    apply RayClass.Modulus.ext
    · simpa only [RayClass.Modulus.finitePart_eraseRealPlaces,
        fullConductor] using hfinite
    · simpa only [RayClass.Modulus.infinitePart_eraseRealPlaces,
        fullConductor, s] using
        Finset.sdiff_sdiff_eq_self hsubset
  rw [← hmod]
  exact hmErase

open scoped Classical in
/-- A modulus is defining exactly when it is at least the full conductor. -/
theorem isDefiningModulus_iff_fullConductor_le
    (H : ConductorialSubgroup K) (m : RayClass.Modulus K) :
    IsDefiningModulus H.1 m ↔ H.fullConductor ≤ m := by
  constructor
  · intro hm
    exact
      ⟨H.narrowFiniteConductor_le hm,
        H.fullConductorInfinitePart_subset_of_isDefiningModulus hm⟩
  · intro hm
    exact
      (RayClass.Modulus.congruenceSubgroup_antitone hm).trans
        H.fullConductor_isDefiningModulus

end ConductorialSubgroup

end GlobalClassFields
end GlobalClassFieldTheory
