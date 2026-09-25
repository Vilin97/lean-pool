/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.PrimeGeneration
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassPrimeIdele
/-!
# Frobenius generation of ray class groups

Prime idèle classes away from a modulus determine homomorphisms out of the
ray class group.  This follows from factorization of prime-to-modulus
fractional ideals and the idelic-to-ideal ray-class equivalence.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory.GlobalClassFields

universe u v

open scoped Classical in
/-- Two homomorphisms out of a ray class group agree if they agree on the
normalized prime idèle classes away from its modulus. -/
theorem rayClassGroup_hom_ext_finitePrime
    {K : Type u} [Field K] [NumberField K]
    (m : RayClass.Modulus K)
    {G : Type v} [CommGroup G]
    (f g : RayClass.RayClassGroup m →* G)
    (hprime : ∀ (v : HeightOneSpectrum (𝓞 K))
      (_ : v ∉ m.finitePart.support),
        f (QuotientGroup.mk' m.congruenceSubgroup
          (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
            (IdeleGroup.finitePrimeIdele v))) =
          g (QuotientGroup.mk' m.congruenceSubgroup
            (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
              (IdeleGroup.finitePrimeIdele v)))) :
    f = g := by
  let e := RayClass.rayClassGroupEquivIdealRayClassGroup m
  let q : RayClass.primeToModulusIdeals m →*
      RayClass.IdealRayClassGroup m :=
    QuotientGroup.mk' (RayClass.principalRayIdealSubgroup m)
  have hprimeIdeal (v : HeightOneSpectrum (𝓞 K))
      (hv : v ∉ m.finitePart.support) :
      e.symm (q (RayClass.primeToModulusIdeal m v hv)) =
        QuotientGroup.mk' m.congruenceSubgroup
          (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
            (IdeleGroup.finitePrimeIdele v)) := by
    apply e.injective
    rw [e.apply_symm_apply]
    calc
      q (RayClass.primeToModulusIdeal m v hv) =
          RayClass.idealRayProjection m
            ⟨IdeleGroup.finitePrimeIdele v,
              finitePrimeIdele_mem_idelePrimeToModulusSubgroup m v hv⟩ :=
        (idealRayProjection_finitePrimeIdele m v hv).symm
      _ = e (QuotientGroup.mk' m.congruenceSubgroup
          (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
            (IdeleGroup.finitePrimeIdele v))) :=
        (rayClassGroupEquivIdealRayClassGroup_mk_primeTo m
          ⟨IdeleGroup.finitePrimeIdele v,
            finitePrimeIdele_mem_idelePrimeToModulusSubgroup m v hv⟩).symm
  have hcomp :
      f.comp (e.symm.toMonoidHom.comp q) =
        g.comp (e.symm.toMonoidHom.comp q) := by
    apply RayClass.primeToModulusIdeals_hom_ext m
    intro v hv
    change f (e.symm (q (RayClass.primeToModulusIdeal m v hv))) =
      g (e.symm (q (RayClass.primeToModulusIdeal m v hv)))
    rw [hprimeIdeal v hv]
    exact hprime v hv
  apply MonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := e.symm.surjective x
  obtain ⟨I, rfl⟩ := QuotientGroup.mk'_surjective
    (RayClass.principalRayIdealSubgroup m) y
  exact DFunLike.congr_fun hcomp I

end GlobalClassFieldTheory.GlobalClassFields
