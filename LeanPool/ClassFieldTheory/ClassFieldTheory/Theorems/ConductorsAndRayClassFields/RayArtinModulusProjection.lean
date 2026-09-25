/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayArtin
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassIdealModulusProjection
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassIdealModulusProjectionPrime
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.PrimeGeneration
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtin
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin
/-!
# Naturality of ray Artin maps under reduction of the modulus

An embedding between two realizations of ray class fields intertwines the
Artin action with the canonical projection of ray class groups.  The
statement uses only Mathlib and public Definitions vocabulary; the idelic
implementation appears only in the proof.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

open scoped Classical in
private local instance rayClassGroupCommGroup
    {K : Type} [Field K] [NumberField K]
    (m : RayClassModulus K) : CommGroup (RayClassGroup m) :=
  { (inferInstance : Group (RayClassGroup m)) with mul_comm := mul_comm' }

attribute [local instance] rayClassGroupCommGroup

open scoped Classical in
private theorem rayArtin_prime_eq_arithmeticPrimeArtin
    {K : Type} [Field K] [NumberField K]
    {m : RayClassModulus K} (R : RayClassFieldRealization K m)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    R.rayArtin (rayClassOfFinitePrime m v hv) =
      GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := R.extension) v := by
  let w₀ := _root_.chosenFinitePlaceExtension (L := R.extension) v
  let w := _root_.finitePlaceExtensionCentre (K := K) (L := R.extension) v w₀
  have hw : w.asIdeal.LiesOver v.asIdeal :=
    _root_.finitePlaceExtensionCentre_liesOver
      (K := K) (L := R.extension) v w₀
  have hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
    (R.unramifiedOutsideModulus.1 v hv) w.asIdeal inferInstance hw
  calc
    R.rayArtin (rayClassOfFinitePrime m v hv) =
        arithmeticFrobeniusAt (K := K) w := R.artin_frobenius v hv w hw
    _ = GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
          (K := K) (L := R.extension) v :=
      (GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
        (K := K) (L := R.extension) v w hw hunram).symm

open scoped Classical in
private theorem arithmeticPrimeArtin_restrict_tower
    {K E L : Type}
    [Field K] [NumberField K]
    [Field E] [NumberField E]
    [Field L] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [IsAbelianGalois K E] [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    AlgEquiv.restrictNormalHom E
        (GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
          (K := K) (L := L) v) =
      GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := E) v := by
  open GlobalClassFieldTheory.GlobalClassFields in
  rw [arithmeticFinitePlacePrimeArtin_eq_inv (K := K) (L := L) v,
    arithmeticFinitePlacePrimeArtin_eq_inv (K := K) (L := E) v, map_inv]
  simpa only [GlobalClassFieldTheory.GlobalClassFields.finitePlacePrimeArtin,
    MonoidHom.comp_apply] using
    congrArg Inv.inv
      (DFunLike.congr_fun
        (GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_restrict_tower
          (K := K) (L := L) (E := E))
        (IdeleGroup.finitePrimeIdele v))

open scoped Classical in
private theorem rayClassGroup_hom_ext_of_prime
    {K : Type} [Field K] [NumberField K]
    {G : Type} [CommGroup G]
    (n : RayClassModulus K)
    (f g : RayClassGroup n →* G)
    (hprime : ∀ (v : HeightOneSpectrum (𝓞 K))
      (hv : v ∉ n.finitePart.support),
        f (rayClassOfFinitePrime n v hv) =
          g (rayClassOfFinitePrime n v hv)) :
    f = g := by
  let n' := GlobalClassFieldComparison.rayClassModulusToOriginal K n
  let e := GlobalClassFieldComparison.rayClassGroupEquivOriginal K n
  let ι : RayClass.primeToModulusIdeals n' →* RayClassGroup n :=
    e.symm.toMonoidHom.comp
      (QuotientGroup.mk' (RayClass.principalRayIdealSubgroup n'))
  have hιprime (v : HeightOneSpectrum (𝓞 K))
      (hv : v ∉ n.finitePart.support) :
      ι (RayClass.primeToModulusIdeal n' v hv) =
        rayClassOfFinitePrime n v hv := by
    apply e.injective
    calc
      e (ι (RayClass.primeToModulusIdeal n' v hv)) =
          QuotientGroup.mk' (RayClass.principalRayIdealSubgroup n')
            (RayClass.primeToModulusIdeal n' v hv) := by
        change e (e.symm
          (QuotientGroup.mk' (RayClass.principalRayIdealSubgroup n')
            (RayClass.primeToModulusIdeal n' v hv))) = _
        exact e.apply_symm_apply _
      _ = e (rayClassOfFinitePrime n v hv) :=
        (GlobalClassFieldComparison.rayClassGroupEquivOriginal_prime
          K n v hv).symm
  have hι : Function.Surjective ι := by
    intro q
    obtain ⟨I, hI⟩ :=
      QuotientGroup.mk'_surjective
        (RayClass.principalRayIdealSubgroup n') (e q)
    refine ⟨I, ?_⟩
    apply e.injective
    change e (e.symm
      (QuotientGroup.mk' (RayClass.principalRayIdealSubgroup n') I)) = e q
    rw [e.apply_symm_apply]
    exact hI
  have hcomp : f.comp ι = g.comp ι := by
    refine RayClass.primeToModulusIdeals_hom_ext
      (G := G) n' (f.comp ι) (g.comp ι) ?_
    intro v hv
    change f (ι (RayClass.primeToModulusIdeal n' v hv)) =
      g (ι (RayClass.primeToModulusIdeal n' v hv))
    rw [hιprime v hv]
    exact hprime v hv
  apply MonoidHom.ext
  intro q
  obtain ⟨I, rfl⟩ := hι q
  exact congrArg
    (fun h : RayClass.primeToModulusIdeals n' →* G => h I) hcomp

open scoped Classical in
/-- Artin reciprocity commutes with reduction of the modulus along any
embedding of the corresponding ray class field realizations. -/
theorem rayArtin_modulusProjection
    {K : Type} [Field K] [NumberField K]
    {m n : RayClassModulus K} (hmn : m ≤ n)
    (Rm : RayClassFieldRealization K m)
    (Rn : RayClassFieldRealization K n)
    (f : Rm.extension →ₐ[K] Rn.extension)
    (x : RayClassGroup n) (y : Rm.extension) :
    Rn.rayArtin x (f y) =
      f (Rm.rayArtin (rayClassIdealModulusProjection K hmn x) y) := by
  let : Algebra Rm.extension Rn.extension := f.toRingHom.toAlgebra
  let : IsScalarTower K Rm.extension Rn.extension :=
    IsScalarTower.of_algebraMap_eq fun z => (f.commutes z).symm
  let : CommGroup (Rm.extension ≃ₐ[K] Rm.extension) :=
    { (inferInstance : Group (Rm.extension ≃ₐ[K] Rm.extension)) with
      mul_comm := mul_comm' }
  have hnat :
      (AlgEquiv.restrictNormalHom Rm.extension).comp Rn.rayArtin =
        Rm.rayArtin.comp (rayClassIdealModulusProjection K hmn) := by
    apply rayClassGroup_hom_ext_of_prime n
    intro v hvn
    have hvm : v ∉ m.finitePart.support := by
      intro hv
      exact hvn (Finsupp.support_mono hmn.1 hv)
    change AlgEquiv.restrictNormalHom Rm.extension
      (Rn.rayArtin (rayClassOfFinitePrime n v hvn)) =
      Rm.rayArtin
        (rayClassIdealModulusProjection K hmn
          (rayClassOfFinitePrime n v hvn))
    rw [rayClassIdealModulusProjection_prime K hmn v hvn,
      rayArtin_prime_eq_arithmeticPrimeArtin Rn v hvn,
      rayArtin_prime_eq_arithmeticPrimeArtin Rm v hvm]
    exact arithmeticPrimeArtin_restrict_tower v
  have hx := DFunLike.congr_fun hnat x
  change AlgEquiv.restrictNormalHom Rm.extension (Rn.rayArtin x) =
    Rm.rayArtin (rayClassIdealModulusProjection K hmn x) at hx
  have hy := congrArg (fun σ : Rm.extension ≃ₐ[K] Rm.extension => f (σ y)) hx
  exact (AlgEquiv.restrictNormal_commutes (Rn.rayArtin x) Rm.extension y).symm.trans hy

end ClassFieldTheory
