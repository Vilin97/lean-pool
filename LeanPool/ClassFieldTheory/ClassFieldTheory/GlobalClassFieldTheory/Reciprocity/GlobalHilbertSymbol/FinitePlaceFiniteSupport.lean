/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.FinitePlaceCharacterComparison
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteIdeleArtin
/-!
# Finite support of finite-place Hilbert symbols

The finite-place Hilbert-symbol family is obtained by applying the Kummer
root character to the finite-place Artin factors of a principal idele.  Its
finite support therefore follows directly from the existing finite-support
theorem for those Artin factors; no second ramification-support construction
is needed here.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open KummerTheory
open Function

variable (K : Type) [Field K] [NumberField K]

open scoped Classical in
/-- For fixed global units `a` and `b`, the finite-place Hilbert symbols are
nontrivial at only finitely many finite places. -/
theorem finitePlaceHilbertSymbol_hasFiniteMulSupport
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : Kˣ) :
    HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 K) =>
        finitePlaceHilbertSymbol K n hnK hmu v a b) := by
  let L := chosenSimpleKummerExtension K n hnK b
  let _ : FiniteDimensional K L :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let _ : IsAbelianGalois K L :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let _ : NumberField L := NumberField.of_module_finite K L
  let chi : Gal(L/K) →* nthRootsSubgroup K (n : ℕ) :=
    (nthRootsSubgroupEquivOfPrimitiveRoots K L n hmu).symm.toMonoidHom.comp
      (chosenSimpleKummerRootCharacter K n hnK hmu b)
  have hArtin :
      HasFiniteMulSupport
        (fun v : HeightOneSpectrum (𝓞 K) =>
          chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v
            (IdeleGroup.finiteComponent v
              (IdeleGroup.principalIdele K a))) :=
    finitePlaceArtinFactors_hasFiniteMulSupport
      (K := K) (L := L) (IdeleGroup.principalIdele K a)
  have hRoot :
      HasFiniteMulSupport
        (fun v : HeightOneSpectrum (𝓞 K) =>
          chi
            (chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v
              (IdeleGroup.finiteComponent v
                (IdeleGroup.principalIdele K a)))) :=
    hArtin.fun_comp chi.map_one
  convert hRoot using 1
  funext v
  have hcomponent :
      (IdeleGroup.finiteComponent v (IdeleGroup.principalIdele K a) :
          (v.adicCompletion K)ˣ) =
        Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a := by
    apply Units.ext
    calc
      ((IdeleGroup.finiteComponent v (IdeleGroup.principalIdele K a) :
          (v.adicCompletion K)ˣ) : v.adicCompletion K) =
          ((a : K) : v.adicCompletion K) :=
        IdeleGroup.finiteComponent_principalIdele a v
      _ = algebraMap K (v.adicCompletion K) (a : K) := by
        symm
        have hmap := congrFun
          (IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion
            (R := 𝓞 K) (S := K) (K := K) (v := v)) (a : K)
        simpa using hmap
  rw [hcomponent]
  calc
    finitePlaceHilbertSymbol K n hnK hmu v a b =
        finitePlaceKummerRootCharacter K n hnK hmu v a b :=
      (finitePlaceKummerRootCharacter_localGlobal
        K n hnK hmu v a b).symm
    _ = chi
        (chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a)) := by
      change finitePlaceKummerRootCharacter K n hnK hmu v a b =
        finitePlaceKummerRootCharacterOfExtension K n hnK hmu v a b
          (chosenFinitePlaceExtension (L := L) v)
      exact
        (finitePlaceKummerRootCharacterOfExtension_eq K n hnK hmu v a b
          (chosenFinitePlaceExtension (L := L) v)).symm

end Reciprocity
end GlobalClassFieldTheory
