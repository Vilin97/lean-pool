/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.FinitePlaceFiniteSupport
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.InfinitePlaceRealComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtinCompatibility
/-!
# The global Hilbert product formula

The finite- and infinite-place Hilbert factors constructed in the preceding
files all take values in the same group of `n`-th roots of unity in the base
field.  Their product is the image, under the global Kummer root character,
of the product of the corresponding local Artin factors.  Global reciprocity
on a principal idele therefore makes this product equal to one.
-/

@[expose] public section

open scoped BigOperators IsMulCommutative NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open KummerTheory

variable (K : Type) [Field K] [NumberField K]

open scoped Classical in
private theorem map_product_mul_finprod
    {I J M N : Type} [Fintype I] [CommMonoid M] [CommMonoid N]
    (chi : M →* N) (f : I → M) (g : J → M)
    (hg : Function.HasFiniteMulSupport g) :
    (∏ i, chi (f i)) * ∏ᶠ j, chi (g j) =
      chi ((∏ i, f i) * ∏ᶠ j, g j) := by
  rw [chi.map_mul, map_prod, MonoidHom.map_finprod chi hg]

open scoped Classical in
/-- The product of the Hilbert symbols of two global units over all places.
The finite-place part is a genuine finite-support product. -/
noncomputable def globalHilbertProduct
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : Kˣ) :
    nthRootsSubgroup K (n : ℕ) :=
  (∏ v : InfinitePlace K,
      infinitePlaceHilbertSymbol K n v a b) *
    ∏ᶠ v : HeightOneSpectrum (𝓞 K),
      finitePlaceHilbertSymbol K n hnK hmu v a b

open scoped Classical in
/-- The global Hilbert product of a principal pair is trivial.  The proof
maps the chosen local Artin product through the global Kummer root character
and then uses the finite- and infinite-place comparison theorems. -/
theorem globalHilbertProduct_principal
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : Kˣ) :
    globalHilbertProduct K n hnK hmu a b = 1 := by
  let L := chosenSimpleKummerExtension K n hnK b
  let : FiniteDimensional K L :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let : IsAbelianGalois K L :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let : NumberField L := NumberField.of_module_finite K L
  let chi : Gal(L/K) →* nthRootsSubgroup K (n : ℕ) :=
    (nthRootsSubgroupEquivOfPrimitiveRoots K L n hmu).symm.toMonoidHom.comp
      (chosenSimpleKummerRootCharacter K n hnK hmu b)
  have hArtin :=
    chosenLocalArtin_product_principalIdele
      (K := K) (L := L) a
  have hFiniteSupport := finitePlaceArtinFactors_hasFiniteMulSupport
    (K := K) (L := L) (IdeleGroup.principalIdele K a)
  have hMapped :
      (∏ v : InfinitePlace K,
          chi
            (chosenInfinitePlaceArtinMonoidHom (K := K) (L := L) v
              (IdeleGroup.infiniteComponent v
                (IdeleGroup.principalIdele K a)))) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          chi
            (chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v
              (IdeleGroup.finiteComponent v
                (IdeleGroup.principalIdele K a))) = 1 := by
    calc
      _ = chi
          ((∏ v : InfinitePlace K,
            chosenInfinitePlaceArtinMonoidHom (K := K) (L := L) v
              (IdeleGroup.infiniteComponent v
                (IdeleGroup.principalIdele K a))) *
          ∏ᶠ v : HeightOneSpectrum (𝓞 K),
            chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v
              (IdeleGroup.finiteComponent v
                (IdeleGroup.principalIdele K a))) :=
        map_product_mul_finprod chi _ _ hFiniteSupport
      _ = chi 1 := congrArg chi hArtin
      _ = 1 := chi.map_one
  have hInfinite :
      (∏ v : InfinitePlace K,
        chi
          (chosenInfinitePlaceArtinMonoidHom (K := K) (L := L) v
            (IdeleGroup.infiniteComponent v
              (IdeleGroup.principalIdele K a)))) =
        ∏ v : InfinitePlace K,
          infinitePlaceHilbertSymbol K n v a b := by
    apply Finset.prod_congr rfl
    intro v _
    have hcomponent :
        (IdeleGroup.infiniteComponent v (IdeleGroup.principalIdele K a) :
            v.Completionˣ) =
          Units.map (algebraMap K v.Completion).toMonoidHom a := by
      apply Units.ext
      calc
        ((IdeleGroup.infiniteComponent v (IdeleGroup.principalIdele K a) :
            v.Completionˣ) : v.Completion) =
            ((a : K) : v.Completion) :=
          IdeleGroup.infiniteComponent_principalIdele a v
        _ = algebraMap K v.Completion (a : K) :=
          (NumberField.InfinitePlace.Completion.algebraMap_apply
            v (a : K)).symm
    rw [hcomponent]
    calc
      chi
          (chosenInfinitePlaceArtinMonoidHom (K := K) (L := L) v
            (Units.map (algebraMap K v.Completion).toMonoidHom a)) =
          infinitePlaceKummerRootCharacter K n hnK hmu v a b := by
        rfl
      _ = infinitePlaceHilbertSymbol K n v a b :=
        infinitePlaceKummerRootCharacter_localGlobal
          K n hnK hmu v a b
  have hFinite :
      (∏ᶠ v : HeightOneSpectrum (𝓞 K),
        chi
          (chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v
            (IdeleGroup.finiteComponent v
              (IdeleGroup.principalIdele K a)))) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          finitePlaceHilbertSymbol K n hnK hmu v a b := by
    apply finprod_congr
    intro v
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
              (𝓞 K) K (S := K) v) (a : K)
          simpa using hmap
    rw [hcomponent]
    calc
      chi
          (chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v
            (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a)) =
          finitePlaceKummerRootCharacter K n hnK hmu v a b := by
        change finitePlaceKummerRootCharacterOfExtension K n hnK hmu v a b
          (chosenFinitePlaceExtension (L := L) v) =
            finitePlaceKummerRootCharacter K n hnK hmu v a b
        exact finitePlaceKummerRootCharacterOfExtension_eq K n hnK hmu v a b
          (chosenFinitePlaceExtension (L := L) v)
      _ = finitePlaceHilbertSymbol K n hnK hmu v a b :=
        finitePlaceKummerRootCharacter_localGlobal
          K n hnK hmu v a b
  unfold globalHilbertProduct
  rw [← hInfinite, ← hFinite]
  exact hMapped

open scoped Classical in
/-- The Hilbert symbols of two global units have product one over all finite
and infinite places. -/
theorem hilbertSymbol_allPlaces_product_eq_one
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : Kˣ) :
    (∏ v : InfinitePlace K,
        infinitePlaceHilbertSymbol K n v a b) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        finitePlaceHilbertSymbol K n hnK hmu v a b = 1 := by
  exact globalHilbertProduct_principal K n hnK hmu a b

end Reciprocity
end GlobalClassFieldTheory
