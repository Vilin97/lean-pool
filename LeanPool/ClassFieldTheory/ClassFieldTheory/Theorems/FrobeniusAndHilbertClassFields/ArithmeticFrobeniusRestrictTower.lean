/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtin
/-!
# Arithmetic Frobenius in a finite abelian tower

At a prime unramified in the top field, restriction of arithmetic Frobenius
to an intermediate field is arithmetic Frobenius at the prime below it.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

open NumberField IsDedekindDomain IdeleGroup
open GlobalClassFieldTheory.GlobalClassFields

private theorem arithmeticFinitePlacePrimeArtin_restrict_tower_of_globalArtin
    (K E L : Type) [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [IsAbelianGalois K E] [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    AlgEquiv.restrictNormalHom E
        (arithmeticFinitePlacePrimeArtin (K := K) (L := L) v) =
      arithmeticFinitePlacePrimeArtin (K := K) (L := E) v := by
  rw [arithmeticFinitePlacePrimeArtin_eq_inv (K := K) (L := L) v,
    arithmeticFinitePlacePrimeArtin_eq_inv (K := K) (L := E) v, map_inv]
  simpa only [finitePlacePrimeArtin, MonoidHom.comp_apply] using
    congrArg Inv.inv
      (DFunLike.congr_fun
        (GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_restrict_tower
          (K := K) (L := L) (E := E))
        (IdeleGroup.finitePrimeIdele v))

/-- In a finite abelian tower `K ⊆ E ⊆ L`, arithmetic Frobenius at an
unramified prime of `L` restricts to arithmetic Frobenius at the specified
prime of `E` below it. -/
theorem arithmeticFrobeniusAt_restrict_tower
    {K E L : Type}
    [Field K] [NumberField K]
    [Field E] [NumberField E]
    [Field L] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [IsAbelianGalois K E] [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (wE : HeightOneSpectrum (𝓞 E))
    (wL : HeightOneSpectrum (𝓞 L))
    (hwE : wE.asIdeal.LiesOver v.asIdeal)
    (hwL : wL.asIdeal.LiesOver wE.asIdeal)
    (hunram : Algebra.IsUnramifiedAt (𝓞 K) wL.asIdeal) :
    AlgEquiv.restrictNormalHom E (arithmeticFrobeniusAt (K := K) wL) =
      arithmeticFrobeniusAt (K := K) wE := by
  have : wL.asIdeal.LiesOver wE.asIdeal := hwL
  have hwLv : wL.asIdeal.LiesOver v.asIdeal :=
    Ideal.LiesOver.trans wL.asIdeal wE.asIdeal v.asIdeal
  have hunramE : Algebra.IsUnramifiedAt (𝓞 K) wE.asIdeal :=
    Algebra.IsUnramifiedAt.of_liesOver (𝓞 K) wE.asIdeal wL.asIdeal
  calc
    AlgEquiv.restrictNormalHom E (arithmeticFrobeniusAt (K := K) wL) =
        AlgEquiv.restrictNormalHom E
          (arithmeticFinitePlacePrimeArtin (K := K) (L := L) v) := by
            rw [GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
              v wL hwLv hunram]
    _ = arithmeticFinitePlacePrimeArtin (K := K) (L := E) v :=
      arithmeticFinitePlacePrimeArtin_restrict_tower_of_globalArtin K E L v
    _ = arithmeticFrobeniusAt (K := K) wE :=
      GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
        v wE hwE hunramE

end ClassFieldTheory
