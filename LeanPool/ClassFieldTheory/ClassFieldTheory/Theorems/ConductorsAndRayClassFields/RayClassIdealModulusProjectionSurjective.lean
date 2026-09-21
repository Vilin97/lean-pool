/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassIdealModulusProjection
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassIdealModulusProjectionPrime
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.PrimeGeneration
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
/-!
# Surjectivity of the ideal-theoretic modulus projection

The direct ideal-quotient projection agrees with the natural idelic quotient
projection because both preserve every prime class outside the larger modulus.
The latter projection is directly surjective since both ray class groups are
quotients of the same idèle class group.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u

private local instance rayClassGroupCommGroup
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) : CommGroup (RayClassGroup m) :=
  { (inferInstance : Group (RayClassGroup m)) with mul_comm := mul_comm' }

private theorem rayClassGroup_hom_ext_of_prime
    (K : Type u) [Field K] [NumberField K]
    (n m : RayClassModulus K)
    (f g : RayClassGroup n →* RayClassGroup m)
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
      (G := RayClassGroup m) n' (f.comp ι) (g.comp ι) ?_
    intro v hv
    change f (ι (RayClass.primeToModulusIdeal n' v hv)) =
      g (ι (RayClass.primeToModulusIdeal n' v hv))
    rw [hιprime v hv]
    exact hprime v hv
  apply MonoidHom.ext
  intro q
  obtain ⟨I, rfl⟩ := hι q
  exact congrArg
    (fun h : RayClass.primeToModulusIdeals n' →* RayClassGroup m => h I) hcomp

/-- Reducing a ray modulus gives a surjection of ideal-theoretic ray class
groups. -/
theorem rayClassIdealModulusProjection_surjective
    (K : Type u) [Field K] [NumberField K]
    {m n : RayClassModulus K} (hmn : m ≤ n) :
    Function.Surjective (rayClassIdealModulusProjection K hmn) := by
  let m' := GlobalClassFieldComparison.rayClassModulusToOriginal K m
  let n' := GlobalClassFieldComparison.rayClassModulusToOriginal K n
  have hmn' : m' ≤ n' := hmn
  let : IsMulCommutative (IdeleClassGroup K) :=
    ⟨⟨fun a b => mul_comm a b⟩⟩
  let : (RayClass.Modulus.congruenceSubgroup m').Normal :=
    Subgroup.normal_of_isMulCommutative _
  let : (RayClass.Modulus.congruenceSubgroup n').Normal :=
    Subgroup.normal_of_isMulCommutative _
  let projection : RayClass.RayClassGroup n' →* RayClass.RayClassGroup m' :=
    QuotientGroup.map
      (RayClass.Modulus.congruenceSubgroup n')
      (RayClass.Modulus.congruenceSubgroup m')
      (MonoidHom.id (IdeleClassGroup K))
      (RayClass.Modulus.congruenceSubgroup_antitone hmn')
  have hprojection : Function.Surjective projection := by
    intro q
    obtain ⟨c, rfl⟩ :=
      QuotientGroup.mk'_surjective
        (RayClass.Modulus.congruenceSubgroup m') q
    exact
      ⟨QuotientGroup.mk' (RayClass.Modulus.congruenceSubgroup n') c, rfl⟩
  let eM := GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m
  let eN := GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K n
  let transported : RayClassGroup n →* RayClassGroup m :=
    eM.symm.toMonoidHom.comp (projection.comp eN.toMonoidHom)
  have htransported : Function.Surjective transported := by
    intro y
    obtain ⟨z, hz⟩ := eM.symm.surjective y
    obtain ⟨w, hw⟩ := hprojection z
    obtain ⟨x, hx⟩ := eN.surjective w
    refine ⟨x, ?_⟩
    change eM.symm (projection (eN x)) = y
    rw [hx, hw, hz]
  have hmap : rayClassIdealModulusProjection K hmn = transported := by
    apply rayClassGroup_hom_ext_of_prime K n m
    intro v hvn
    rw [rayClassIdealModulusProjection_prime K hmn v hvn]
    apply eM.injective
    change
      eM (rayClassOfFinitePrime m v _) =
        eM (eM.symm (projection (eN (rayClassOfFinitePrime n v hvn))))
    rw [eM.apply_symm_apply,
      GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele_prime K m v,
      GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele_prime K n v hvn]
    rfl
  rw [hmap]
  exact htransported

end ClassFieldTheory
