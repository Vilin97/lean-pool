/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayPrimeGeneration
/-!
# Prime classes determine maps out of a ray class group

Finite primes away from the modulus generate enough of the ideal-theoretic
ray class group to determine any homomorphism into a commutative group.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable
section

namespace ClassFieldTheory

universe u v

/-- Two homomorphisms from a ray class group agree if they have the same
value on every prime class away from the modulus. -/
theorem rayClassGroup_hom_ext_finitePrime
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K)
    {G : Type v} [CommGroup G]
    (f g : RayClassGroup m →* G)
    (hprime : ∀ (v : HeightOneSpectrum (𝓞 K))
      (hv : v ∉ m.finitePart.support),
        f (rayClassOfFinitePrime m v hv) =
          g (rayClassOfFinitePrime m v hv)) :
    f = g := by
  let m' := GlobalClassFieldComparison.rayClassModulusToOriginal K m
  let e := GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m
  have hcomp : f.comp e.symm.toMonoidHom = g.comp e.symm.toMonoidHom := by
    apply GlobalClassFieldTheory.GlobalClassFields.rayClassGroup_hom_ext_finitePrime m'
    intro v hv
    have hv' : v ∉ m.finitePart.support := hv
    change f (e.symm (QuotientGroup.mk' m'.congruenceSubgroup
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
          (IdeleGroup.finitePrimeIdele v)))) =
      g (e.symm (QuotientGroup.mk' m'.congruenceSubgroup
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
          (IdeleGroup.finitePrimeIdele v))))
    rw [← GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele_prime
      K m v hv']
    simpa only [e, MulEquiv.symm_apply_apply] using hprime v hv'
  apply MonoidHom.ext
  intro x
  have hx := DFunLike.congr_fun hcomp (e x)
  change f (e.symm (e x)) = g (e.symm (e x)) at hx
  simpa only [MulEquiv.symm_apply_apply] using hx

end ClassFieldTheory
