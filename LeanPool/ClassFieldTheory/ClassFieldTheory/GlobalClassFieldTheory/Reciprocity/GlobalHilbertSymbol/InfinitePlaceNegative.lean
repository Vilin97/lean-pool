/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.InfinitePlaceNegativeUnit
/-!
# The negative-negative real infinite-place Hilbert factor
-/

open scoped NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open KummerTheory

variable (K : Type) [Field K] [NumberField K]

open scoped Classical in
/-- In the quadratic real case with both arguments negative, the actual
infinite-place Kummer root character is `-1`. -/
theorem infinitePlaceKummerRootCharacter_eq_neg_one_of_real_of_neg_neg
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : InfinitePlace K) (a b : Kˣ)
    (hn : (n : ℕ) = 2) (hv : v.IsReal)
    (ha : InfinitePlace.embedding_of_isReal hv (a : K) < 0)
    (hb : InfinitePlace.embedding_of_isReal hv (b : K) < 0) :
    let negOne : nthRootsSubgroup K (n : ℕ) :=
      ⟨(-1 : Kˣ), by simp [hn]⟩
    infinitePlaceKummerRootCharacter K n hnK hmu v a b = negOne := by
  let L := chosenSimpleKummerExtension K n hnK b
  let : FiniteDimensional K L :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let : IsAbelianGalois K L :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let : NumberField L := NumberField.of_module_finite K L
  let a_v : v.Completionˣ :=
    Units.map (algebraMap K v.Completion).toMonoidHom a
  let beta : Lˣ := chosenSimpleKummerRootUnit K n hnK b
  let sigma : Gal(L/K) :=
    chosenInfinitePlaceArtinMonoidHom (K := K) (L := L) v a_v
  let negOne : nthRootsSubgroup K (n : ℕ) :=
    ⟨(-1 : Kˣ), by simp [hn]⟩
  have hArtin :
      sigma = chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v (-1 : v.Completionˣ) := by
    exact chosenInfinitePlaceArtin_globalUnit_eq_neg_one_of_real_of_neg
      K v hv a ha
  have haction :
      chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v (-1 : v.Completionˣ) (beta : L) =
        -(beta : L) := by
    change
      chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v (-1 : v.Completionˣ)
            ((chosenSimpleKummerRootUnit K n hnK b : Lˣ) : L) =
        -((chosenSimpleKummerRootUnit K n hnK b : Lˣ) : L)
    exact
      chosenInfinitePlaceArtin_neg_one_apply_kummerRoot_of_real_of_radical_neg
        K n hnK hmu v b hn hv hb
  have hroot :
      rootQuotient (K := K) (L := L) beta sigma =
        Units.map (algebraMap K L).toMonoidHom negOne.1 := by
    apply Units.ext
    simp only [rootQuotient, Units.val_div_eq_div_val, Units.coe_map]
    change sigma (beta : L) / (beta : L) =
      algebraMap K L (-1 : K)
    rw [hArtin, haction]
    simp
  apply nthRootsSubgroupMap_injective K L (n : ℕ)
  change
    nthRootsSubgroupMap K L (n : ℕ)
        ((nthRootsSubgroupEquivOfPrimitiveRoots K L n hmu).symm
          (chosenSimpleKummerRootCharacter K n hnK hmu b sigma)) =
      nthRootsSubgroupMap K L (n : ℕ) negOne
  calc
    nthRootsSubgroupMap K L (n : ℕ)
        ((nthRootsSubgroupEquivOfPrimitiveRoots K L n hmu).symm
          (chosenSimpleKummerRootCharacter K n hnK hmu b sigma)) =
        chosenSimpleKummerRootCharacter K n hnK hmu b sigma := by
      exact
        (nthRootsSubgroupEquivOfPrimitiveRoots K L n hmu).apply_symm_apply _
    _ = nthRootsSubgroupMap K L (n : ℕ) negOne := by
      apply Subtype.ext
      rw [chosenSimpleKummerRootCharacter_apply]
      exact hroot

open scoped Classical in
/-- The explicit Hilbert factor and the Kummer root character agree in the
negative-negative quadratic real branch. -/
theorem infinitePlaceKummerRootCharacter_localGlobal_of_real_of_neg_neg
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : InfinitePlace K) (a b : Kˣ)
    (hn : (n : ℕ) = 2) (hv : v.IsReal)
    (ha : InfinitePlace.embedding_of_isReal hv (a : K) < 0)
    (hb : InfinitePlace.embedding_of_isReal hv (b : K) < 0) :
    infinitePlaceKummerRootCharacter K n hnK hmu v a b =
      infinitePlaceHilbertSymbol K n v a b := by
  let negOne : nthRootsSubgroup K (n : ℕ) :=
    ⟨(-1 : Kˣ), by simp [hn]⟩
  calc
    infinitePlaceKummerRootCharacter K n hnK hmu v a b = negOne :=
      infinitePlaceKummerRootCharacter_eq_neg_one_of_real_of_neg_neg
        K n hnK hmu v a b hn hv ha hb
    _ = infinitePlaceHilbertSymbol K n v a b := by
      apply Subtype.ext
      simp [negOne, infinitePlaceHilbertSymbol, hn, hv, ha, hb]

end Reciprocity
end GlobalClassFieldTheory
