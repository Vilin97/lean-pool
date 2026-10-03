/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.IdealArtinMap
/-!
# The ideal Artin quotient

For a defining modulus `m`, the ideal-theoretic Artin map is surjective and
has kernel `H_m`.  The first isomorphism theorem therefore identifies
`J_K^m / H_m` with the corresponding idelic norm quotient `C_K / N`.
-/

@[expose] public section

open scoped NumberField

noncomputable
section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open NumberField

variable {K : Type} [Field K] [NumberField K]

-- Reuse the normality witness embedded in the imported ideal-Artin definitions.
-- Choosing a different generic witness here makes quotient equivalences compare
-- enormous, propositionally equal but non-definitional terms.
attribute [local instance] ideleClassSubgroupNormal

local instance idealArtinKernelNormal
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    (idealArtinKernel m N hm).Normal := by
  change (idealArtinMap m N hm).ker.Normal
  infer_instance

/-- The ideal class-field isomorphism
`J_K^m / H_m ≃ C_K / N`. -/
noncomputable def idealClassQuotientEquivNormQuotient
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    RayClass.primeToModulusIdeals m ⧸
        idealArtinKernel m N hm ≃*
      IdeleClassGroup K ⧸ N := by
  have hker :
      idealArtinKernel m N hm =
        (idealArtinMap m N hm).ker :=
    rfl
  exact
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (idealArtinMap m N hm)
        (idealArtinMap_surjective m N hm))

/-- The ideal class-field equivalence sends a quotient representative to
its ideal Artin image. -/
theorem idealClassQuotientEquivNormQuotient_mk
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N)
    (a : RayClass.primeToModulusIdeals m) :
    idealClassQuotientEquivNormQuotient m N hm
        (QuotientGroup.mk' (idealArtinKernel m N hm) a) =
      idealArtinMap m N hm a :=
  rfl

/-- The Artin kernel is exactly the equivalence relation defining the
ideal class-field quotient. -/
theorem idealClassQuotient_mk_eq_one_iff
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N)
    (a : RayClass.primeToModulusIdeals m) :
    QuotientGroup.mk' (idealArtinKernel m N hm) a = 1 ↔
      idealArtinMap m N hm a = 1 := by
  exact
    (QuotientGroup.eq_one_iff a).trans
      (((idealArtin_exact m N hm).1 a).symm)

section ActualGaloisQuotient

variable
    {L : Type} [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

/-- The ideal class-field isomorphism with the actual Galois group:
`J_K^m / H_m ≃ Gal(L/K)`.

Its first factor is the ideal/idèle norm-quotient comparison, and its
second factor is the genuine global norm-residue equivalence. -/
noncomputable def idealClassQuotientEquivGaloisGroup
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    RayClass.primeToModulusIdeals m ⧸
        idealArtinKernel m
          ((_root_.ideleClassNorm K L).range) hm ≃*
      (L ≃ₐ[K] L) :=
  (idealClassQuotientEquivNormQuotient m
      ((_root_.ideleClassNorm K L).range) hm).trans
    (AddEquiv.toMultiplicative
      (Reciprocity.globalNormResidueEquiv K L))

/-- On a representative ideal, the actual ideal class-field
isomorphism evaluates to the genuine Galois-valued ideal Artin map. -/
theorem idealClassQuotientEquivGaloisGroup_mk
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (a : RayClass.primeToModulusIdeals m) :
    idealClassQuotientEquivGaloisGroup
        (K := K) (L := L) m hm
        (QuotientGroup.mk'
          (idealArtinKernel m
            ((_root_.ideleClassNorm K L).range) hm) a) =
      idealArtinGaloisMap (K := K) (L := L) m hm a :=
  rfl

/-- An ideal class is trivial in the class-field quotient exactly when
its actual Galois-valued Artin symbol is trivial. -/
theorem idealClassQuotient_mk_eq_one_iff_galoisArtin_eq_one
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (a : RayClass.primeToModulusIdeals m) :
    QuotientGroup.mk'
          (idealArtinKernel m
            ((_root_.ideleClassNorm K L).range) hm) a =
        1 ↔
      idealArtinGaloisMap
          (K := K) (L := L) m hm a =
        1 := by
  exact
    (QuotientGroup.eq_one_iff a).trans
      (((idealArtinGalois_exact
        (K := K) (L := L) m hm).1 a).symm)

end ActualGaloisQuotient

end IdealClassFieldTheory
end GlobalClassFieldTheory
