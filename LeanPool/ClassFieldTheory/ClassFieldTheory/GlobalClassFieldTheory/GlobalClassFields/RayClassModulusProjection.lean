/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassFieldRealization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
public import Mathlib.Data.Finsupp.Order
/-!
# Projection between ray class groups

The idèle-class quotient gives the canonical map from a larger ray modulus
to a smaller one. The public ray-class groups use the comparison equivalence
to transport this map.
-/

@[expose] public section

open scoped NumberField
noncomputable
section

namespace ClassFieldTheory

open NumberField IsDedekindDomain

variable (K : Type) [Field K] [NumberField K]

open scoped Classical in
local instance ideleClassIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] ideleClassIsMulCommutative

open scoped Classical in
local instance rayCongruenceNormal (m : RayClass.Modulus K) :
    (RayClass.Modulus.congruenceSubgroup m).Normal :=
  Subgroup.normal_of_isMulCommutative _

attribute [local instance] rayCongruenceNormal

open scoped Classical in
/-- The quotient projection between the original idèle-class ray groups. -/
def originalRayClassModulusProjection
    {m n : RayClass.Modulus K} (hmn : m ≤ n) :
    RayClass.RayClassGroup n →* RayClass.RayClassGroup m :=
  QuotientGroup.map
    (RayClass.Modulus.congruenceSubgroup n)
    (RayClass.Modulus.congruenceSubgroup m)
    (MonoidHom.id (IdeleClassGroup K))
    (RayClass.Modulus.congruenceSubgroup_antitone hmn)

open scoped Classical in
/-- The projection of the original idèle-class ray groups is onto. -/
theorem originalRayClassModulusProjection_surjective
    {m n : RayClass.Modulus K} (hmn : m ≤ n) :
    Function.Surjective (originalRayClassModulusProjection K hmn) := by
  intro q
  obtain ⟨c, rfl⟩ :=
    QuotientGroup.mk'_surjective (RayClass.Modulus.congruenceSubgroup m) q
  exact
    ⟨QuotientGroup.mk' (RayClass.Modulus.congruenceSubgroup n) c, rfl⟩

open scoped Classical in
/-- For `m ≤ n`, the natural quotient map from the ray class group modulo
`n` onto the ray class group modulo `m`. -/
noncomputable def rayClassModulusProjection
    {m n : RayClassModulus K} (hmn : m ≤ n) :
    RayClassGroup n →* RayClassGroup m := by
  let m' := GlobalClassFieldComparison.rayClassModulusToOriginal K m
  let n' := GlobalClassFieldComparison.rayClassModulusToOriginal K n
  have hmn' : m' ≤ n' := hmn
  exact
    (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).symm.toMonoidHom.comp
      ((originalRayClassModulusProjection K hmn').comp
        (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K n).toMonoidHom)

open scoped Classical in
/-- Evaluate the public projection through the original idèle-class quotient. -/
theorem rayClassModulusProjection_apply
    {m n : RayClassModulus K} (hmn : m ≤ n)
    (a : RayClassGroup n) :
    rayClassModulusProjection K hmn a =
      (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).symm
        (originalRayClassModulusProjection K
          (show GlobalClassFieldComparison.rayClassModulusToOriginal K m ≤
            GlobalClassFieldComparison.rayClassModulusToOriginal K n from hmn)
          (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K n a)) :=
  rfl

open scoped Classical in
/-- The modulus-change projection is onto. -/
theorem rayClassModulusProjection_surjective
    {m n : RayClassModulus K} (hmn : m ≤ n) :
    Function.Surjective (rayClassModulusProjection K hmn) := by
  let m' := GlobalClassFieldComparison.rayClassModulusToOriginal K m
  let n' := GlobalClassFieldComparison.rayClassModulusToOriginal K n
  have hmn' : m' ≤ n' := hmn
  intro y
  obtain ⟨z, hz⟩ :=
    originalRayClassModulusProjection_surjective K hmn'
      (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m y)
  refine ⟨(GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K n).symm z, ?_⟩
  calc
    rayClassModulusProjection K hmn
        ((GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K n).symm z) =
      (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).symm
        (originalRayClassModulusProjection K hmn'
          (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K n
            ((GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K n).symm z))) :=
      rayClassModulusProjection_apply K hmn _
    _ =
      (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).symm
        (originalRayClassModulusProjection K hmn' z) := by
      rw [(GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K n).apply_symm_apply]
    _ =
      (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).symm
        (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m y) :=
      congrArg
        (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).symm hz
    _ = y :=
      (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).symm_apply_apply y

open scoped Classical in
/-- The image of a prime ray class under modulus change is the same prime
ray class, provided the prime is outside the larger modulus. -/
theorem rayClassModulusProjection_prime
    {m n : RayClassModulus K} (hmn : m ≤ n)
    (v : HeightOneSpectrum (𝓞 K))
    (hvn : v ∉ n.finitePart.support) :
    rayClassModulusProjection K hmn
        (rayClassOfFinitePrime n v hvn) =
      rayClassOfFinitePrime m v
        (by
          intro hvm
          exact hvn (Finsupp.support_mono hmn.1 hvm)) := by
  have hvm : v ∉ m.finitePart.support := by
    intro hv
    exact hvn (Finsupp.support_mono hmn.1 hv)
  let m' := GlobalClassFieldComparison.rayClassModulusToOriginal K m
  let n' := GlobalClassFieldComparison.rayClassModulusToOriginal K n
  have hmn' : m' ≤ n' := hmn
  apply (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).injective
  change
    (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m)
      ((GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).symm
        (originalRayClassModulusProjection K hmn'
          (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K n
            (rayClassOfFinitePrime n v hvn)))) =
      GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m
        (rayClassOfFinitePrime m v hvm)
  rw [(GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).apply_symm_apply]
  rw [GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele_prime K n v hvn]
  rw [GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele_prime K m v hvm]
  rfl

open scoped Classical in
/-- Enlarging the public modulus gives literal containment of the selected
ray class fields inside the fixed separable closure. -/
theorem chosenRayClassFieldSubfield_mono
    {m n : RayClassModulus K} (hmn : m ≤ n) :
    GlobalClassFieldTheory.GlobalClassFields.rayClassFieldSubfield K
        (GlobalClassFieldComparison.rayClassModulusToOriginal K m) ≤
      GlobalClassFieldTheory.GlobalClassFields.rayClassFieldSubfield K
        (GlobalClassFieldComparison.rayClassModulusToOriginal K n) := by
  apply GlobalClassFieldTheory.GlobalClassFields.rayClassFieldSubfield_mono
  exact hmn

end ClassFieldTheory
