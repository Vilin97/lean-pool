/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.NormLimitationStatement
/-!
# Proof core for ideal norm limitation

This leaf proves the packaged statement using the idèle-class norm-range
equality and the finite-extension ideal Artin kernel theorem.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

variable
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

private theorem idealArtinKernel_congr
    (m : RayClass.Modulus K)
    {N P : Subgroup (IdeleClassGroup K)}
    (hN : RayClass.Modulus.congruenceSubgroup m ≤ N)
    (hP : RayClass.Modulus.congruenceSubgroup m ≤ P)
    (hNP : N = P) :
    idealArtinKernel m N hN = idealArtinKernel m P hP := by
  subst P
  rfl

/-- Core proof of the packaged ideal norm-limitation statement. -/
theorem idealNormSubgroupMaximalAbelianStatement_proof
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    idealNormSubgroupMaximalAbelianStatement K L m hm := by
  unfold idealNormSubgroupMaximalAbelianStatement
  let A := finiteNormalClosureMaximalAbelianSubfield K L
  have hRange :
      (_root_.ideleClassNorm K L).range =
        (_root_.ideleClassNorm K A).range :=
    GlobalClassFields.ideleClassNorm_range_eq_maximalAbelianSubfield K L
  have hmA :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K A).range :=
    hRange ▸ hm
  calc
    RayClass.idealNormSubgroup (K := K) (L := L) m =
        idealArtinKernel m
          ((_root_.ideleClassNorm K L).range) hm :=
      (idealArtinKernel_eq_idealNormSubgroup_of_finiteExtension
        (K := K) (L := L) m hm).symm
    _ = idealArtinKernel m
          ((_root_.ideleClassNorm K A).range) hmA :=
      idealArtinKernel_congr
        (K := K) (m := m)
        (N := (_root_.ideleClassNorm K L).range)
        (P := (_root_.ideleClassNorm K A).range)
        hm hmA hRange
    _ = RayClass.idealNormSubgroup (K := K) (L := A) m :=
      idealArtinKernel_eq_idealNormSubgroup_of_finiteExtension
        (K := K) (L := A) m hmA

end IdealClassFieldTheory
end GlobalClassFieldTheory
