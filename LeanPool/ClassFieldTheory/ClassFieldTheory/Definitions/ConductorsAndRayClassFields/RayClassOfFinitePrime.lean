/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.NarrowRayClassModulus
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.OrdinaryRayClassModulus
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeFractionalIdeal
/-!
# Prime classes in ray class groups
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u

private lemma finitePrimeFractionalIdeal_mem_primeTo
    {K : Type u} [Field K] [NumberField K]
    (m : RayClassModulus K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    finitePrimeFractionalIdeal v ∈ rayClassPrimeToIdeals m := by
  intro w hw
  exact FractionalIdeal.count_maximal_coprime K w fun h => (h ▸ hv) hw

/-- The class in the ray class group represented by a finite prime away from
the modulus. -/
def rayClassOfFinitePrime
    {K : Type u} [Field K] [NumberField K]
    (m : RayClassModulus K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) : RayClassGroup m :=
  QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m)
    ⟨finitePrimeFractionalIdeal v, finitePrimeFractionalIdeal_mem_primeTo m v hv⟩

/-- The ordinary ideal class represented by a finite prime. -/
def ordinaryRayClassOfFinitePrime
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    RayClassGroup (ordinaryRayClassModulus K) :=
  rayClassOfFinitePrime (ordinaryRayClassModulus K) v (by
    simp [ordinaryRayClassModulus])

/-- The narrow ideal class represented by a finite prime. -/
def narrowRayClassOfFinitePrime
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    RayClassGroup (narrowRayClassModulus K) :=
  rayClassOfFinitePrime (narrowRayClassModulus K) v (by
    simp [narrowRayClassModulus])

end ClassFieldTheory
