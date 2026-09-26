/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Residue Field -/

@[expose] public section
namespace ValuationTheory

/-!
# Residue-field API for local maps

This file adds reusable local-ring residue-field lemmas that are used by the
Henselian and unramified parts of the DVF library.  It keeps mathlib's
`IsLocalRing.ResidueField.map` and `IsLocalRing.residue` as the primary
objects.
-/

noncomputable
section

universe u v w

namespace DiscreteValuationField
namespace ResidueField

variable {R : Type u} {S : Type v} {T : Type w}

section LocalRing

variable [CommRing R] [IsLocalRing R]

/-- Equality in the residue field is equality modulo the maximal ideal. -/
theorem residue_eq_residue_iff_sub_mem_maximalIdeal (x y : R) :
    IsLocalRing.residue R x = IsLocalRing.residue R y ↔
      x - y ∈ IsLocalRing.maximalIdeal R := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]

/-- The residue of a difference is zero exactly when the two residues are
equal. -/
theorem residue_sub_eq_zero_iff (x y : R) :
    IsLocalRing.residue R (x - y) = 0 ↔
      IsLocalRing.residue R x = IsLocalRing.residue R y := by
  rw [IsLocalRing.residue_eq_zero_iff,
    residue_eq_residue_iff_sub_mem_maximalIdeal]

end LocalRing

section FieldLift

variable [CommRing R] [IsLocalRing R] [Field S]
variable (f : R →+* S) [IsLocalHom f]

/-- The map from the residue field induced by a local homomorphism to a field is
uniquely characterized by its composite with the residue map. -/
theorem lift_eq_of_comp_residue_eq
    (g : IsLocalRing.ResidueField R →+* S)
    (hg : g.comp (IsLocalRing.residue R) = f) :
    g = IsLocalRing.ResidueField.lift f := by
  ext x
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  have hr := congr_arg (fun h : R →+* S => h r) hg
  simpa [RingHom.comp_apply, IsLocalRing.ResidueField.lift_residue_apply] using hr

end FieldLift

section LocalHom

variable [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
variable (f : R →+* S) [IsLocalHom f]

/-- A local homomorphism pulls back the target maximal ideal to the source
maximal ideal. -/
theorem comap_maximalIdeal_eq :
    (IsLocalRing.maximalIdeal S).comap f = IsLocalRing.maximalIdeal R :=
  IsLocalRing.maximalIdeal_comap f

/-- A local homomorphism induces an injective map on residue fields. -/
theorem map_injective :
    Function.Injective (IsLocalRing.ResidueField.map f) := by
  intro x y hxy
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective y
  rw [IsLocalRing.ResidueField.map_residue,
    IsLocalRing.ResidueField.map_residue] at hxy
  rw [residue_eq_residue_iff_sub_mem_maximalIdeal]
  have hsubS : f (r - s) ∈ IsLocalRing.maximalIdeal S := by
    rw [map_sub]
    exact
      (residue_eq_residue_iff_sub_mem_maximalIdeal
        (R := S) (f r) (f s)).1 hxy
  have hpre : r - s ∈ (IsLocalRing.maximalIdeal S).comap f := hsubS
  rwa [comap_maximalIdeal_eq f] at hpre

/-- A residue-field map induced by a local homomorphism has trivial kernel. -/
theorem map_eq_zero_iff (x : IsLocalRing.ResidueField R) :
    IsLocalRing.ResidueField.map f x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    exact map_injective f (by simpa using hx)
  · intro hx
    rw [hx, map_zero]

/-- Equality can be checked after applying the residue-field map induced by a
local homomorphism. -/
theorem map_eq_map_iff (x y : IsLocalRing.ResidueField R) :
    IsLocalRing.ResidueField.map f x = IsLocalRing.ResidueField.map f y ↔
      x = y := by
  constructor
  · intro hxy
    exact map_injective f hxy
  · intro h
    rw [h]

/-- The residue-field isomorphism induced by a surjective residue-field map
coming from a local homomorphism. -/
noncomputable def ringEquivOfSurjective
    (hsurj : Function.Surjective (IsLocalRing.ResidueField.map f)) :
    IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField S :=
  RingEquiv.ofBijective (IsLocalRing.ResidueField.map f)
    ⟨map_injective f, hsurj⟩

/-- The residue-ring equivalence induced by a surjective map evaluates by that map. -/
@[simp]
theorem ringEquivOfSurjective_apply
    (hsurj : Function.Surjective (IsLocalRing.ResidueField.map f))
    (x : IsLocalRing.ResidueField R) :
    ringEquivOfSurjective f hsurj x =
      IsLocalRing.ResidueField.map f x :=
  rfl

/-- A local homomorphism preserves and reflects zero residues. -/
theorem residue_map_eq_zero_iff (x : R) :
    IsLocalRing.residue S (f x) = 0 ↔ IsLocalRing.residue R x = 0 := by
  rw [← IsLocalRing.ResidueField.map_residue f x]
  exact map_eq_zero_iff f (IsLocalRing.residue R x)

/-- A local homomorphism preserves and reflects equality of residues. -/
theorem residue_map_eq_iff (x y : R) :
    IsLocalRing.residue S (f x) = IsLocalRing.residue S (f y) ↔
      IsLocalRing.residue R x = IsLocalRing.residue R y := by
  simpa [IsLocalRing.ResidueField.map_residue f] using
    map_eq_map_iff f (IsLocalRing.residue R x) (IsLocalRing.residue R y)

/-- A mapped residue class equals a target residue class exactly when their
chosen representatives are congruent modulo the target maximal ideal. -/
theorem map_residue_eq_residue_iff_sub_mem_maximalIdeal (x : R) (y : S) :
    IsLocalRing.ResidueField.map f (IsLocalRing.residue R x) =
        IsLocalRing.residue S y ↔
      f x - y ∈ IsLocalRing.maximalIdeal S := by
  simpa [IsLocalRing.ResidueField.map_residue f x] using
    residue_eq_residue_iff_sub_mem_maximalIdeal (R := S) (f x) y

/-- Target residue equality with a mapped residue class, in the opposite
orientation, is also equality modulo the target maximal ideal. -/
theorem residue_eq_map_residue_iff_sub_mem_maximalIdeal (y : S) (x : R) :
    IsLocalRing.residue S y =
        IsLocalRing.ResidueField.map f (IsLocalRing.residue R x) ↔
      y - f x ∈ IsLocalRing.maximalIdeal S := by
  simpa [IsLocalRing.ResidueField.map_residue f x] using
    residue_eq_residue_iff_sub_mem_maximalIdeal (R := S) y (f x)

end LocalHom

section Algebra

variable [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
variable [Algebra R S] [IsLocalHom (algebraMap R S)]

/-- For a local algebra map, mathlib's residue-field algebra map agrees with
the residue-field map induced by the structure homomorphism. -/
theorem algebraMap_eq_map_algebraMap :
    algebraMap (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S) =
      IsLocalRing.ResidueField.map (algebraMap R S) := by
  ext x
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  simp [IsLocalRing.ResidueField.map_residue,
    IsLocalRing.ResidueField.algebraMap_residue]

/-- The residue-field map induced by a local algebra map is injective. -/
theorem map_algebraMap_injective :
    Function.Injective
      (IsLocalRing.ResidueField.map (algebraMap R S)) :=
  map_injective (algebraMap R S)

/-- The residue-field map induced by a local algebra map has trivial
kernel. -/
theorem map_algebraMap_eq_zero_iff (x : IsLocalRing.ResidueField R) :
    IsLocalRing.ResidueField.map (algebraMap R S) x = 0 ↔ x = 0 :=
  map_eq_zero_iff (algebraMap R S) x

/-- A local algebra map preserves and reflects zero residues. -/
theorem residue_algebraMap_eq_zero_iff (x : R) :
    IsLocalRing.residue S (algebraMap R S x) = 0 ↔
      IsLocalRing.residue R x = 0 :=
  residue_map_eq_zero_iff (algebraMap R S) x

/-- A local algebra map preserves and reflects equality of residues. -/
theorem residue_algebraMap_eq_iff (x y : R) :
    IsLocalRing.residue S (algebraMap R S x) =
        IsLocalRing.residue S (algebraMap R S y) ↔
      IsLocalRing.residue R x = IsLocalRing.residue R y :=
  residue_map_eq_iff (algebraMap R S) x y

/-- The residue-field algebra map sends the residue of `x` to the residue of
`y` exactly when `algebraMap R S x` and `y` are congruent modulo the target
maximal ideal. -/
theorem algebraMap_residue_eq_residue_iff_sub_mem_maximalIdeal
    (x : R) (y : S) :
    algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
        (IsLocalRing.residue R x) = IsLocalRing.residue S y ↔
      algebraMap R S x - y ∈ IsLocalRing.maximalIdeal S := by
  rw [algebraMap_eq_map_algebraMap]
  exact map_residue_eq_residue_iff_sub_mem_maximalIdeal (algebraMap R S) x y

end Algebra

section AlgEquiv

variable [CommRing T] [IsLocalRing T]
variable [CommRing R] [IsLocalRing R] [Algebra T R]
variable [CommRing S] [IsLocalRing S] [Algebra T S]
variable [IsLocalHom (algebraMap T R)] [IsLocalHom (algebraMap T S)]

/-- A local algebra equivalence induces an algebra equivalence on residue
fields over the base residue field. -/
noncomputable def algEquivOfAlgEquiv
    (e : R ≃ₐ[T] S) :
    IsLocalRing.ResidueField R ≃ₐ[IsLocalRing.ResidueField T]
      IsLocalRing.ResidueField S := by
  letI : IsLocalHom (e.toRingEquiv : R →+* S) :=
    IsLocalHom.of_surjective (e.toRingEquiv : R →+* S) e.surjective
  letI : IsLocalHom (e.symm.toRingEquiv : S →+* R) :=
    IsLocalHom.of_surjective (e.symm.toRingEquiv : S →+* R) e.symm.surjective
  exact
    { IsLocalRing.ResidueField.mapEquiv e.toRingEquiv with
      commutes' := by
        intro x
        obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective x
        simp [IsLocalRing.ResidueField.algebraMap_residue,
          IsLocalRing.ResidueField.map_residue, e.commutes t] }

/-- The residue-field equivalence induced by an algebra equivalence acts through
residue representatives. -/
@[simp]
theorem algEquivOfAlgEquiv_apply
    (e : R ≃ₐ[T] S)
    (x : IsLocalRing.ResidueField R) :
    algEquivOfAlgEquiv e x =
      IsLocalRing.ResidueField.map e.toRingEquiv x :=
  rfl

/-- The induced residue algebra equivalence agrees with the canonical quotient-map equivalence. -/
theorem algEquivOfAlgEquiv_apply_eq_mapEquiv
    (e : R ≃ₐ[T] S)
    (x : IsLocalRing.ResidueField R) :
    algEquivOfAlgEquiv e x =
      IsLocalRing.ResidueField.mapEquiv e.toRingEquiv x :=
  rfl

/-- The inverse induced residue equivalence agrees with the inverse quotient-map equivalence. -/
theorem algEquivOfAlgEquiv_symm_apply_eq_mapEquiv
    (e : R ≃ₐ[T] S)
    (x : IsLocalRing.ResidueField S) :
    (algEquivOfAlgEquiv e).symm x =
      IsLocalRing.ResidueField.mapEquiv e.symm.toRingEquiv x :=
  rfl

/-- The induced residue equivalence sends the residue of an integral element to
its transported residue. -/
@[simp]
theorem algEquivOfAlgEquiv_apply_residue
    (e : R ≃ₐ[T] S) (x : R) :
    algEquivOfAlgEquiv e (IsLocalRing.residue R x) =
      IsLocalRing.residue S (e x) := by
  let : IsLocalHom (e.toRingEquiv : R →+* S) :=
    IsLocalHom.of_surjective (e.toRingEquiv : R →+* S) e.surjective
  change IsLocalRing.ResidueField.map e.toRingEquiv
      (IsLocalRing.residue R x) = IsLocalRing.residue S (e x)
  rfl

/-- The inverse induced residue equivalence sends residues back along the inverse
algebra equivalence. -/
theorem algEquivOfAlgEquiv_symm_apply_residue
    (e : R ≃ₐ[T] S) (x : S) :
    (algEquivOfAlgEquiv e).symm (IsLocalRing.residue S x) =
      IsLocalRing.residue R (e.symm x) := by
  let : IsLocalHom (e.symm.toRingEquiv : S →+* R) :=
    IsLocalHom.of_surjective (e.symm.toRingEquiv : S →+* R) e.symm.surjective
  rw [algEquivOfAlgEquiv_symm_apply_eq_mapEquiv]
  change IsLocalRing.ResidueField.map e.symm.toRingEquiv
      (IsLocalRing.residue S x) = IsLocalRing.residue R (e.symm x)
  rfl

/-- Passing to residue fields commutes with inversion of algebra equivalences. -/
@[simp]
theorem algEquivOfAlgEquiv_symm
    (e : R ≃ₐ[T] S) :
    (algEquivOfAlgEquiv e).symm = algEquivOfAlgEquiv e.symm := by
  ext x
  rfl

/-- The identity algebra equivalence induces the identity on residue fields. -/
@[simp]
theorem algEquivOfAlgEquiv_refl :
    algEquivOfAlgEquiv (AlgEquiv.refl : R ≃ₐ[T] R) =
      (AlgEquiv.refl :
        IsLocalRing.ResidueField R ≃ₐ[IsLocalRing.ResidueField T]
          IsLocalRing.ResidueField R) := by
  ext x
  simp [algEquivOfAlgEquiv]

/-- Residue-field equivalences respect composition of algebra equivalences. -/
@[simp]
theorem algEquivOfAlgEquiv_trans
    {U : Type*} [CommRing U] [IsLocalRing U] [Algebra T U]
    [IsLocalHom (algebraMap T U)]
    (eRS : R ≃ₐ[T] S) (eSU : S ≃ₐ[T] U) :
    (algEquivOfAlgEquiv eRS).trans (algEquivOfAlgEquiv eSU) =
      algEquivOfAlgEquiv (eRS.trans eSU) := by
  ext x
  rw [algEquivOfAlgEquiv]
  exact congr_arg (fun f => f x)
    (IsLocalRing.ResidueField.mapEquiv_trans
      eRS.toRingEquiv eSU.toRingEquiv).symm

end AlgEquiv

end ResidueField
end DiscreteValuationField

end

end ValuationTheory
