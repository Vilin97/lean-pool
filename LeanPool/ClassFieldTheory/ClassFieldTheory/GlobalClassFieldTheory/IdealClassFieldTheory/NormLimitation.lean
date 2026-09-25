/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.NormLimitationCore
/-!
# Ideal and ray consequences of norm limitation

For a finite extension `L / K`, norm limitation identifies its idèle-class
norm range with that of the maximal abelian subfield in the chosen finite
normal closure.  This leaf transports that equality to the corresponding
ideal norm group for every defining modulus and to the image of the norm
range in every ray class group.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

private theorem normLimitationIdeleClassIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] normLimitationIdeleClassIsMulCommutative

variable
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The norm subgroup in the ray class group is the image of the actual
idèle-class norm range modulo the ray congruence subgroup. -/
noncomputable def rayNormSubgroup (m : RayClass.Modulus K) :
    Subgroup (RayClass.RayClassGroup m) :=
  Subgroup.map
    (QuotientGroup.mk'
      (RayClass.Modulus.congruenceSubgroup m))
    ((_root_.ideleClassNorm K L).range)

omit [FiniteDimensional K L] in
/-- For a defining modulus, the ray norm subgroup is exactly the kernel of
the canonical map from the ray class group to the idèle-class norm
quotient. -/
theorem rayNormSubgroup_eq_rayClassToNormQuotient_ker
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    rayNormSubgroup K L m =
      (rayClassToNormQuotient m
        ((_root_.ideleClassNorm K L).range) hm).ker := by
  unfold rayNormSubgroup rayClassToNormQuotient
  let N := RayClass.Modulus.congruenceSubgroup m
  let M := (_root_.ideleClassNorm K L).range
  change
    Subgroup.map (QuotientGroup.mk' N) M =
      (QuotientGroup.map N M (MonoidHom.id (IdeleClassGroup K)) _).ker
  symm
  simpa only [Subgroup.comap_id] using
    (QuotientGroup.ker_map (N := N) M
      (MonoidHom.id (IdeleClassGroup K))
      (show N ≤ Subgroup.comap (MonoidHom.id (IdeleClassGroup K)) M from
        by simpa only [N, M, Subgroup.comap_id] using hm))

/-- Ideal norm limitation: for every defining modulus, the genuine ideal
norm group of a finite extension equals that of its maximal abelian
subfield in the chosen finite normal closure. -/
theorem idealNormSubgroup_eq_maximalAbelianSubfield
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    idealNormSubgroupMaximalAbelianStatement K L m hm :=
  idealNormSubgroupMaximalAbelianStatement_proof K L m hm

/-- Ray norm limitation: the image of a finite extension's idèle-class norm
range in every ray class group is already the image of the norm range from
its maximal abelian subfield. -/
theorem rayNormSubgroup_eq_maximalAbelianSubfield
    (m : RayClass.Modulus K) :
    rayNormSubgroup K L m =
      rayNormSubgroup K
        (finiteNormalClosureMaximalAbelianSubfield K L) m := by
  unfold rayNormSubgroup
  rw [GlobalClassFields.ideleClassNorm_range_eq_maximalAbelianSubfield K L]

end IdealClassFieldTheory
end GlobalClassFieldTheory
