/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Abelianization.Defs

/-! # Transfer Naturality -/

@[expose] public section
namespace ClassFormation

/-!
# Naturality of transfer under a quotient

This file supplies the group-theoretic source used in transfer--norm naturality. If a surjection
has kernel contained in a finite-index subgroup, it identifies the two left-coset spaces and
transfer commutes with the induced maps on abelianizations.
-/

noncomputable section

open Function
open scoped Pointwise

variable {P : Type*} {Q : Type*} [Group P] [Group Q]

/-- A surjection identifies left cosets of `H` with left cosets of its image
when its kernel is contained in `H`. -/
noncomputable def leftCosetEquivMapOfSurjective
    (f : P →* Q) (hf : Function.Surjective f)
    (H : Subgroup P) (hker : f.ker ≤ H) :
    P ⧸ H ≃ Q ⧸ H.map f := by
  let mapCoset : P ⧸ H → Q ⧸ H.map f :=
    Quotient.map' f fun x y hxy => by
      rw [QuotientGroup.leftRel_apply]
      rw [← f.map_inv, ← f.map_mul]
      exact ⟨x⁻¹ * y, (QuotientGroup.leftRel_apply).1 hxy, rfl⟩
  apply Equiv.ofBijective mapCoset
  constructor
  · refine Quotient.ind' fun x => ?_
    refine Quotient.ind' fun y hxy => ?_
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    have hrel : QuotientGroup.leftRel (H.map f) (f x) (f y) :=
      Quotient.eq''.1 hxy
    have hmap : f (x⁻¹ * y) ∈ H.map f := by
      rw [f.map_mul, f.map_inv]
      exact (QuotientGroup.leftRel_apply).1 hrel
    have hcomap : x⁻¹ * y ∈ (H.map f).comap f := hmap
    rwa [Subgroup.comap_map_eq_self hker] at hcomap
  · refine Quotient.ind' fun q => ?_
    obtain ⟨p, rfl⟩ := hf q
    exact ⟨QuotientGroup.mk p, rfl⟩

/--
Establishes the identity `leftCosetEquivMapOfSurjective f hf H hker (QuotientGroup.mk p) =
QuotientGroup.mk (f p)`.
-/
@[simp]
theorem leftCosetEquivMapOfSurjective_mk
    (f : P →* Q) (hf : Function.Surjective f)
    (H : Subgroup P) (hker : f.ker ≤ H) (p : P) :
    leftCosetEquivMapOfSurjective f hf H hker (QuotientGroup.mk p) =
      QuotientGroup.mk (f p) :=
  rfl

/--
Establishes the identity `leftCosetEquivMapOfSurjective f hf H hker (p • q) = f p •
leftCosetEquivMapOfSurjective f hf H hker q`.
-/
@[simp]
theorem leftCosetEquivMapOfSurjective_smul
    (f : P →* Q) (hf : Function.Surjective f)
    (H : Subgroup P) (hker : f.ker ≤ H)
    (p : P) (q : P ⧸ H) :
    leftCosetEquivMapOfSurjective f hf H hker (p • q) =
      f p • leftCosetEquivMapOfSurjective f hf H hker q := by
  refine Quotient.inductionOn' q ?_
  intro x
  simp only [MulAction.Quotient.smul_mk, leftCosetEquivMapOfSurjective_mk,
    smul_eq_mul, map_mul]

/-- A left transversal descends along the same quotient map.  It is built
from the induced equivalence of left-coset spaces, so its chosen
representatives are literally the images of the original representatives. -/
noncomputable def leftTransversalMapOfSurjective
    (f : P →* Q) (hf : Function.Surjective f)
    (H : Subgroup P) (hker : f.ker ≤ H)
    (T : H.LeftTransversal) : (H.map f).LeftTransversal := by
  let e := leftCosetEquivMapOfSurjective f hf H hker
  let u : Q ⧸ H.map f → Q := fun q =>
    f (T.2.leftQuotientEquiv (e.symm q) : P)
  have hu (q : Q ⧸ H.map f) : (u q : Q ⧸ H.map f) = q := by
    change e (QuotientGroup.mk
      (T.2.leftQuotientEquiv (e.symm q) : P)) = q
    have hrep : QuotientGroup.mk
        (T.2.leftQuotientEquiv (e.symm q) : P) = e.symm q :=
      T.2.quotientGroupMk_leftQuotientEquiv (e.symm q)
    exact (congrArg e hrep).trans (e.apply_symm_apply q)
  exact ⟨Set.range u, Subgroup.isComplement_range_left hu⟩

/--
The defining evaluation formula for `leftTransversalMapOfSurjective` is
`((leftTransversalMapOfSurjective f hf H hker T).2.leftQuotientEquiv q : Q) = f
(T.2.leftQuotientEquiv ((leftCosetEquivMapOfSurjective f hf H hker).symm q) : P)`.
-/
@[simp]
theorem leftTransversalMapOfSurjective_apply
    (f : P →* Q) (hf : Function.Surjective f)
    (H : Subgroup P) (hker : f.ker ≤ H)
    (T : H.LeftTransversal) (q : Q ⧸ H.map f) :
    ((leftTransversalMapOfSurjective f hf H hker T).2.leftQuotientEquiv q : Q) =
      f (T.2.leftQuotientEquiv
        ((leftCosetEquivMapOfSurjective f hf H hker).symm q) : P) := by
  let e := leftCosetEquivMapOfSurjective f hf H hker
  let u : Q ⧸ H.map f → Q := fun r =>
    f (T.2.leftQuotientEquiv (e.symm r) : P)
  have hu (r : Q ⧸ H.map f) : (u r : Q ⧸ H.map f) = r := by
    change e (QuotientGroup.mk
      (T.2.leftQuotientEquiv (e.symm r) : P)) = r
    have hrep : QuotientGroup.mk
        (T.2.leftQuotientEquiv (e.symm r) : P) = e.symm r :=
      T.2.quotientGroupMk_leftQuotientEquiv (e.symm r)
    exact (congrArg e hrep).trans (e.apply_symm_apply r)
  change ((Subgroup.isComplement_range_left hu).leftQuotientEquiv q : Q) = u q
  exact Subgroup.IsComplement.leftQuotientEquiv_apply hu q

private theorem leftQuotientEquiv_mk_of_mem
    (H : Subgroup P) (T : H.LeftTransversal) (p : P)
    (hp : p ∈ (T : Set P)) :
    (T.2.leftQuotientEquiv (QuotientGroup.mk p) : P) = p := by
  have heq : T.2.leftQuotientEquiv (QuotientGroup.mk p) =
      (⟨p, hp⟩ : (T : Set P)) := by
    apply T.2.leftQuotientEquiv.symm.injective
    rw [T.2.leftQuotientEquiv.symm_apply_apply]
    rfl
  exact congrArg Subtype.val heq

private theorem mem_leftTransversalMapOfSurjective_iff
    (f : P →* Q) (hf : Function.Surjective f)
    (H : Subgroup P) (hker : f.ker ≤ H)
    (T : H.LeftTransversal) (q : Q) :
    q ∈ (leftTransversalMapOfSurjective f hf H hker T : Set Q) ↔
      ∃ p ∈ (T : Set P), f p = q := by
  let e := leftCosetEquivMapOfSurjective f hf H hker
  change q ∈ Set.range (fun r : Q ⧸ H.map f =>
      f (T.2.leftQuotientEquiv (e.symm r) : P)) ↔ _
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨T.2.leftQuotientEquiv (e.symm r),
      (T.2.leftQuotientEquiv (e.symm r)).2, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    refine ⟨e (QuotientGroup.mk p), ?_⟩
    change f (T.2.leftQuotientEquiv
      (e.symm (e (QuotientGroup.mk p))) : P) = f p
    rw [e.symm_apply_apply, leftQuotientEquiv_mk_of_mem H T p hp]

private theorem leftTransversalMapOfSurjective_smul
    (f : P →* Q) (hf : Function.Surjective f)
    (H : Subgroup P) (hker : f.ker ≤ H)
    (T : H.LeftTransversal) (p : P) :
    leftTransversalMapOfSurjective f hf H hker (p • T) =
      f p • leftTransversalMapOfSurjective f hf H hker T := by
  apply Subtype.ext
  ext q
  rw [mem_leftTransversalMapOfSurjective_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, ht, rfl⟩ := Set.mem_smul_set.mp hx
    have hft := (mem_leftTransversalMapOfSurjective_iff
      f hf H hker T (f t)).2
      ⟨t, ht, rfl⟩
    rw [smul_eq_mul, map_mul]
    change f p * f t ∈
      (f p • (leftTransversalMapOfSurjective f hf H hker T : Set Q) : Set Q)
    exact Set.smul_mem_smul_set hft
  · intro hq
    obtain ⟨t, ht, hpt⟩ := Set.mem_smul_set.mp hq
    subst q
    obtain ⟨x, hx, hfx⟩ :=
      (mem_leftTransversalMapOfSurjective_iff
        f hf H hker T t).1 ht
    refine ⟨p * x, Set.smul_mem_smul_set (a := p) hx, ?_⟩
    simp [map_mul, hfx]

private theorem leftTransversals_diff_natural_of_surjective
    (f : P →* Q) (hf : Function.Surjective f)
    (H : Subgroup P) (hker : f.ker ≤ H) [H.FiniteIndex]
    (S T : H.LeftTransversal) :
    let J := H.map f
    letI : J.FiniteIndex := by
      rw [Subgroup.finiteIndex_iff, H.index_map_eq hf hker]
      exact Subgroup.FiniteIndex.index_ne_zero
    Abelianization.map (f.subgroupMap H)
        (Subgroup.leftTransversals.diff
          (Abelianization.of : H →* Abelianization H) S T) =
      Subgroup.leftTransversals.diff
        (Abelianization.of : J →* Abelianization J)
        (leftTransversalMapOfSurjective f hf H hker S)
        (leftTransversalMapOfSurjective f hf H hker T) := by
  dsimp only
  let : (H.map f).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, H.index_map_eq hf hker]
    exact Subgroup.FiniteIndex.index_ne_zero
  classical
  let : Fintype (P ⧸ H) := H.fintypeQuotientOfFiniteIndex
  let : Fintype (Q ⧸ H.map f) :=
    (H.map f).fintypeQuotientOfFiniteIndex
  let e := leftCosetEquivMapOfSurjective f hf H hker
  simp only [Subgroup.leftTransversals.diff, map_prod,
    Abelianization.map_of, leftTransversalMapOfSurjective_apply]
  rw [← e.prod_comp]
  apply Finset.prod_congr rfl
  intro q _
  apply congrArg Abelianization.of
  apply Subtype.ext
  simp [e]

/-- Transfer is natural for a surjective homomorphism whose kernel is
contained in the finite-index subgroup.  Both transfer maps are Mathlib's
actual `MonoidHom.transfer`; the proof descends an arbitrary left
transversal and compares the defining products term by term. -/
theorem abelianization_transfer_natural_of_surjective
    (f : P →* Q) (hf : Function.Surjective f)
    (H : Subgroup P) (hker : f.ker ≤ H) [H.FiniteIndex] :
    let J := H.map f
    letI : J.FiniteIndex := by
      rw [Subgroup.finiteIndex_iff, H.index_map_eq hf hker]
      exact Subgroup.FiniteIndex.index_ne_zero
    (Abelianization.map (f.subgroupMap H)).comp
        (Abelianization.lift
          (MonoidHom.transfer
            (Abelianization.of : H →* Abelianization H))) =
      (Abelianization.lift
          (MonoidHom.transfer
            (Abelianization.of : J →* Abelianization J))).comp
        (Abelianization.map f) := by
  dsimp only
  let : (H.map f).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, H.index_map_eq hf hker]
    exact Subgroup.FiniteIndex.index_ne_zero
  apply Abelianization.hom_ext
  apply MonoidHom.ext
  intro p
  simp only [MonoidHom.comp_apply, Abelianization.lift_apply_of,
    Abelianization.map_of]
  let T : H.LeftTransversal := default
  rw [MonoidHom.transfer_def
    (Abelianization.of : H →* Abelianization H) T p]
  rw [MonoidHom.transfer_def
    (Abelianization.of : H.map f →* Abelianization (H.map f))
    (leftTransversalMapOfSurjective f hf H hker T) (f p)]
  rw [← leftTransversalMapOfSurjective_smul f hf H hker T p]
  exact leftTransversals_diff_natural_of_surjective
    f hf H hker T (p • T)

/-- Replacing a finite-index subgroup by an equal subgroup only transports
the codomain of transfer along the corresponding canonical equivalence. -/
theorem abelianization_transfer_congr_subgroup
    (H J : Subgroup P) (h : H = J)
    [H.FiniteIndex] [J.FiniteIndex] :
    (MulEquiv.subgroupCongr h).abelianizationCongr.toMonoidHom.comp
        (Abelianization.lift
          (MonoidHom.transfer
            (Abelianization.of : H →* Abelianization H))) =
      Abelianization.lift
        (MonoidHom.transfer
          (Abelianization.of : J →* Abelianization J)) := by
  subst J
  have hc : MulEquiv.subgroupCongr (show H = H from rfl) =
      MulEquiv.refl H := by
    ext x
    rfl
  rw [hc, abelianizationCongr_refl]
  exact MonoidHom.id_comp _

end
end ClassFormation
