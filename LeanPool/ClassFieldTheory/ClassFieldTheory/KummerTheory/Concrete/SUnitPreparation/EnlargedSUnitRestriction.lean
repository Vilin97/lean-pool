/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.FullSUnitKummerExtension
import LeanPool.ClassFieldTheory.ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.FiniteRadicalSupport
/-!
# Restriction from an enlarged S-unit Kummer extension

The concrete embedding and Galois restriction map, its fixing subgroup, and the cyclic fixed
  fields attached to kernel elements.
-/

open scoped NumberField IsMulCommutative NNReal ValuativeRel
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

namespace KummerTheory

variable {K : Type*} [Field K]
    [numberFieldK : NumberField K]

open scoped Classical in
/-- The actual field containment `L ≤ N` for finite S-unit preparation, after producing
the required finite enlargement of `S`. -/
theorem le_fullSUnitKummerExtension_of_enlargedS
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    E ≤
      fullSUnitKummerExtension
        (K := K) (Omega := Omega) n
        (enlargeByFiniteKummerRadicalSupport
          (K := K) (L := E) n hmu S) := by
  have hgenerate :=
    kummerRadicalExtension_enlargedSUnitKummerSubgroup_eq
      (K := K) (Omega := Omega) E n hmu hexponent S
  have hmono := kummerRadicalExtension_mono
    (K := K) (Omega := Omega) n
    (sUnitKummerSubgroup_le_fullSUnitKummerSubgroup
      (K := K) (L := E) n
      (enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S))
  intro x hx
  apply hmono
  rw [hgenerate]
  exact hx

open scoped Classical in
/-- The actual inclusion algebra `E → N` supplied by the source-produced
containment above. -/
@[reducible]
noncomputable def enlargedSUnitKummerAlgebra
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Algebra E
      (fullSUnitKummerExtension
        (K := K) (Omega := Omega) n
        (enlargeByFiniteKummerRadicalSupport
          (K := K) (L := E) n hmu S)) :=
  (IntermediateField.inclusion
    (le_fullSUnitKummerExtension_of_enlargedS
      (K := K) (Omega := Omega) E n hmu hexponent S)).toAlgebra

open scoped Classical in
/-- Restriction from the full `S`-unit Kummer extension `N` to the actual
extension `E ≤ N` produced above. -/
noncomputable def enlargedSUnitKummerRestrictionHom
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Gal(fullSUnitKummerExtension
          (K := K) (Omega := Omega) n
          (enlargeByFiniteKummerRadicalSupport
            (K := K) (L := E) n hmu S)/K) →*
      Gal(E/K) := by
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n
      (enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S)
  let : Algebra E N :=
    enlargedSUnitKummerAlgebra
      (K := K) (Omega := Omega) E n hmu hexponent S
  letI : IsScalarTower K E N := by infer_instance
  exact
    AlgEquiv.restrictNormalHom
      (F := K) (K₁ := N) (E := E)

open scoped Classical in
/-- The restriction map `Gal(N/K) → Gal(E/K)` is onto. -/
theorem enlargedSUnitKummerRestrictionHom_surjective
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective
      (enlargedSUnitKummerRestrictionHom
        (K := K) (Omega := Omega) E n hmu hexponent S) := by
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n
      (enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S)
  let _ : Algebra E N :=
    enlargedSUnitKummerAlgebra
      (K := K) (Omega := Omega) E n hmu hexponent S
  let : IsScalarTower K E N := by infer_instance
  let : IsGalois K N :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n
      (enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S)
  simpa [enlargedSUnitKummerRestrictionHom, N] using
    (AlgEquiv.restrictNormalHom_surjective
      (F := K) (K₁ := E) (E := N))

open scoped Classical in
/-- The actual embedded copy of `E` inside the full `S`-unit Kummer
extension `N`. -/
noncomputable def enlargedSUnitKummerEmbeddedExtension
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IntermediateField K
      (fullSUnitKummerExtension
        (K := K) (Omega := Omega) n
        (enlargeByFiniteKummerRadicalSupport
          (K := K) (L := E) n hmu S)) := by
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n
      (enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S)
  let : Algebra E N :=
    enlargedSUnitKummerAlgebra
      (K := K) (Omega := Omega) E n hmu hexponent S
  let : IsScalarTower K E N := by infer_instance
  exact (IsScalarTower.toAlgHom K E N).fieldRange

open scoped Classical in
/-- The kernel of restriction is precisely the subgroup fixing the
concrete embedded copy of `E` in `N`. -/
theorem enlargedSUnitKummerRestrictionHom_ker_eq_fixingSubgroup
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (enlargedSUnitKummerRestrictionHom
      (K := K) (Omega := Omega) E n hmu hexponent S).ker =
      (enlargedSUnitKummerEmbeddedExtension
        (K := K) (Omega := Omega) E n hmu
        hexponent S).fixingSubgroup := by
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  let _ : Algebra E N :=
    enlargedSUnitKummerAlgebra
      (K := K) (Omega := Omega) E n hmu hexponent S
  let _ : IsScalarTower K E N := by infer_instance
  let M : IntermediateField K N :=
    (IsScalarTower.toAlgHom K E N).fieldRange
  change
    (AlgEquiv.restrictNormalHom
      (F := K) (K₁ := N) (E := E)).ker =
        M.fixingSubgroup
  ext sigma
  rw [MonoidHom.mem_ker,
    IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hsigma y hy
    rcases hy with ⟨x, rfl⟩
    have hx :
        sigma.restrictNormal E x = x := by
      change
        (AlgEquiv.restrictNormalHom
          (F := K) (K₁ := N) (E := E) sigma) x =
            (1 : Gal(E/K)) x
      rw [hsigma]
    calc
      sigma (algebraMap E N x) =
          algebraMap E N (sigma.restrictNormal E x) :=
        (AlgEquiv.restrictNormal_commutes sigma E x).symm
      _ = algebraMap E N x :=
        congrArg (algebraMap E N) hx
  · intro hsigma
    apply AlgEquiv.ext
    intro x
    apply (algebraMap E N).injective
    change
      algebraMap E N (sigma.restrictNormal E x) =
        algebraMap E N x
    exact
      (AlgEquiv.restrictNormal_commutes sigma E x).trans
        (hsigma (algebraMap E N x) ⟨x, rfl⟩)

open scoped Classical in
/-- The field fixed by the concrete restriction kernel is exactly the
embedded copy of `E`. -/
theorem fixedField_enlargedSUnitKummerRestrictionHom_ker
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IntermediateField.fixedField
        (enlargedSUnitKummerRestrictionHom
          (K := K) (Omega := Omega) E n hmu
          hexponent S).ker =
      enlargedSUnitKummerEmbeddedExtension
        (K := K) (Omega := Omega) E n hmu
        hexponent S := by
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : IsGalois K N :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S'
  let : FiniteDimensional K N :=
    fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := Omega) n hnK hmu S'
  rw [
    enlargedSUnitKummerRestrictionHom_ker_eq_fixingSubgroup
      (K := K) (Omega := Omega) E n hmu
      hexponent S]
  exact
    IsGalois.fixedField_fixingSubgroup
      (enlargedSUnitKummerEmbeddedExtension
        (K := K) (Omega := Omega) E n hmu
        hexponent S)

open scoped Classical in
/-- For an element `sigma` of the relative Galois subgroup
`Gal(N/E)`, this is the actual cyclic fixed field
`N_sigma = N ^ ⟨sigma⟩` used in the prime construction of the finite S-unit preparation argument. -/
noncomputable def enlargedSUnitKummerCyclicFixedField
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (sigma :
      (enlargedSUnitKummerRestrictionHom
        (K := K) (Omega := Omega) E n hmu
        hexponent S).ker) :
    IntermediateField K
      (fullSUnitKummerExtension
        (K := K) (Omega := Omega) n
        (enlargeByFiniteKummerRadicalSupport
          (K := K) (L := E) n hmu S)) :=
  IntermediateField.fixedField
    (Subgroup.zpowers
      (sigma :
        Gal(fullSUnitKummerExtension
          (K := K) (Omega := Omega) n
          (enlargeByFiniteKummerRadicalSupport
            (K := K) (L := E) n hmu S)/K)))

open scoped Classical in
/-- The embedded extension `E` lies in every cyclic fixed field attached
to an element of `Gal(N/E)`. -/
theorem enlargedSUnitKummerEmbeddedExtension_le_cyclicFixedField
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (sigma :
      (enlargedSUnitKummerRestrictionHom
        (K := K) (Omega := Omega) E n hmu
        hexponent S).ker) :
    enlargedSUnitKummerEmbeddedExtension
        (K := K) (Omega := Omega) E n hmu
        hexponent S ≤
      enlargedSUnitKummerCyclicFixedField
        (K := K) (Omega := Omega) E n hmu
        hexponent S sigma := by
  apply (IntermediateField.le_iff_le _ _).2
  rw [
    ← enlargedSUnitKummerRestrictionHom_ker_eq_fixingSubgroup
      (K := K) (Omega := Omega) E n hmu
      hexponent S]
  exact Subgroup.zpowers_le.mpr sigma.2

open scoped Classical in
/-- The top Kummer field is Galois over each cyclic fixed field. -/
theorem enlargedSUnitKummerCyclicFixedField_isGalois
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (sigma :
      (enlargedSUnitKummerRestrictionHom
        (K := K) (Omega := Omega) E n hmu
        hexponent S).ker) :
    IsGalois
      (enlargedSUnitKummerCyclicFixedField
        (K := K) (Omega := Omega) E n hmu
        hexponent S sigma)
      (fullSUnitKummerExtension
        (K := K) (Omega := Omega) n
        (enlargeByFiniteKummerRadicalSupport
          (K := K) (L := E) n hmu S)) := by
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : IsGalois K N :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S'
  let : Finite Gal(N/K) :=
    finite_fullSUnitKummerExtension_galois
      (K := K) (Omega := Omega) n hnK hmu S'
  change
    IsGalois
      (IntermediateField.fixedField
        (Subgroup.zpowers (sigma : Gal(N/K)))) N
  exact IsGalois.of_fixed_field N _

open scoped Classical in
/-- The relative degree of `N/N_sigma` is the order of `sigma`. -/
theorem enlargedSUnitKummerCyclicFixedField_finrank
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (sigma :
      (enlargedSUnitKummerRestrictionHom
        (K := K) (Omega := Omega) E n hmu
        hexponent S).ker) :
    Module.finrank
        (enlargedSUnitKummerCyclicFixedField
          (K := K) (Omega := Omega) E n hmu
          hexponent S sigma)
        (fullSUnitKummerExtension
          (K := K) (Omega := Omega) n
          (enlargeByFiniteKummerRadicalSupport
            (K := K) (L := E) n hmu S)) =
      orderOf
        (sigma :
          Gal(fullSUnitKummerExtension
            (K := K) (Omega := Omega) n
            (enlargeByFiniteKummerRadicalSupport
              (K := K) (L := E) n hmu S)/K)) := by
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : FiniteDimensional K N :=
    fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := Omega) n hnK hmu S'
  change
    Module.finrank
        (IntermediateField.fixedField
          (Subgroup.zpowers (sigma : Gal(N/K)))) N =
      orderOf (sigma : Gal(N/K))
  rw [IntermediateField.finrank_fixedField_eq_card,
    Nat.card_zpowers]

open scoped Classical in
/-- The relative Galois group `Gal(N/N_sigma)` is cyclic. -/
theorem enlargedSUnitKummerCyclicFixedField_isCyclic
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (sigma :
      (enlargedSUnitKummerRestrictionHom
        (K := K) (Omega := Omega) E n hmu
        hexponent S).ker) :
    IsCyclic
      ((fullSUnitKummerExtension
          (K := K) (Omega := Omega) n
          (enlargeByFiniteKummerRadicalSupport
            (K := K) (L := E) n hmu S)) ≃ₐ[
        enlargedSUnitKummerCyclicFixedField
          (K := K) (Omega := Omega) E n hmu
          hexponent S sigma]
        (fullSUnitKummerExtension
          (K := K) (Omega := Omega) n
          (enlargeByFiniteKummerRadicalSupport
            (K := K) (L := E) n hmu S))) := by
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : FiniteDimensional K N :=
    fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := Omega) n hnK hmu S'
  let P : Subgroup Gal(N/K) :=
    Subgroup.zpowers (sigma : Gal(N/K))
  have hP : IsCyclic P :=
    Subgroup.isCyclic_zpowers (sigma : Gal(N/K))
  exact
    (IntermediateField.subgroupEquivAlgEquiv P).isCyclic.mp
      hP

open scoped Classical in
/-- The order of every relative automorphism divides the Kummer
exponent `n`. -/
theorem orderOf_enlargedSUnitKummerRestrictionKernel_dvd
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (sigma :
      (enlargedSUnitKummerRestrictionHom
        (K := K) (Omega := Omega) E n hmu
        hexponent S).ker) :
    orderOf
        (sigma :
          Gal(fullSUnitKummerExtension
            (K := K) (Omega := Omega) n
            (enlargeByFiniteKummerRadicalSupport
              (K := K) (L := E) n hmu S)/K)) ∣
      (n : ℕ) :=
  orderOf_dvd_of_pow_eq_one
    (fullSUnitKummerExtension_galois_pow_eq_one
      (K := K) (Omega := Omega) n hmu
      (enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S)
      (sigma :
        Gal(fullSUnitKummerExtension
          (K := K) (Omega := Omega) n
          (enlargeByFiniteKummerRadicalSupport
            (K := K) (L := E) n hmu S)/K)))

open scoped Classical in
/-- If `n = p^v`, then the cyclic degree attached to every relative
automorphism is a power of `p`. -/
theorem exists_orderOf_enlargedSUnitKummerRestrictionKernel_eq_prime_pow
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (p v : ℕ) (hp : p.Prime)
    (hn : (n : ℕ) = p ^ v)
    (sigma :
      (enlargedSUnitKummerRestrictionHom
        (K := K) (Omega := Omega) E n hmu
        hexponent S).ker) :
    ∃ k ≤ v,
      orderOf
          (sigma :
            Gal(fullSUnitKummerExtension
              (K := K) (Omega := Omega) n
              (enlargeByFiniteKummerRadicalSupport
                (K := K) (L := E) n hmu S)/K)) =
        p ^ k := by
  apply (Nat.dvd_prime_pow hp).1
  rw [← hn]
  exact
    orderOf_enlargedSUnitKummerRestrictionKernel_dvd
      (K := K) (Omega := Omega) E n hmu
      hexponent S sigma

open scoped Classical in
/-- A nonidentity relative automorphism gives a genuinely nontrivial
cyclic subextension. -/
theorem enlargedSUnitKummerCyclicFixedField_ne_top
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (sigma :
      (enlargedSUnitKummerRestrictionHom
        (K := K) (Omega := Omega) E n hmu
        hexponent S).ker)
    (hsigma :
      (sigma :
        Gal(fullSUnitKummerExtension
          (K := K) (Omega := Omega) n
          (enlargeByFiniteKummerRadicalSupport
            (K := K) (L := E) n hmu S)/K)) ≠ 1) :
    enlargedSUnitKummerCyclicFixedField
        (K := K) (Omega := Omega) E n hmu
        hexponent S sigma ≠ ⊤ := by
  intro htop
  have hdegree :=
    enlargedSUnitKummerCyclicFixedField_finrank
      (K := K) (Omega := Omega) E n hmu
      hexponent S sigma
  rw [htop, IntermediateField.finrank_top] at hdegree
  exact hsigma (orderOf_eq_one_iff.mp hdegree.symm)

open scoped Classical in
/-- In the prime-power case, a nonidentity relative automorphism has
order `p^k` with positive exponent. -/
theorem exists_pos_orderOf_enlargedSUnitKummerRestrictionKernel_eq_prime_pow
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (p v : ℕ) (hp : p.Prime)
    (hn : (n : ℕ) = p ^ v)
    (sigma :
      (enlargedSUnitKummerRestrictionHom
        (K := K) (Omega := Omega) E n hmu
        hexponent S).ker)
    (hsigma :
      (sigma :
        Gal(fullSUnitKummerExtension
          (K := K) (Omega := Omega) n
          (enlargeByFiniteKummerRadicalSupport
            (K := K) (L := E) n hmu S)/K)) ≠ 1) :
    ∃ k, 0 < k ∧ k ≤ v ∧
      orderOf
          (sigma :
            Gal(fullSUnitKummerExtension
              (K := K) (Omega := Omega) n
              (enlargeByFiniteKummerRadicalSupport
                (K := K) (L := E) n hmu S)/K)) =
        p ^ k := by
  obtain ⟨k, hkv, horder⟩ :=
    exists_orderOf_enlargedSUnitKummerRestrictionKernel_eq_prime_pow
      (K := K) (Omega := Omega) E n hmu
      hexponent S p v hp hn sigma
  have hk : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hkzero
    apply hsigma
    apply orderOf_eq_one_iff.mp
    rw [horder, hkzero, pow_zero]
  exact ⟨k, hk, hkv, horder⟩

end KummerTheory
