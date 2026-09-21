/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.InfinitePlaceCharacter
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.InfinitePlaceRealSquare
import LeanPool.ClassFieldTheory.ClassFieldTheory.KummerTheory.Concrete.SimpleExtensionLocalBehavior
/-!
# The positive-radicand real infinite-place branch

When the radicand is positive at a real place, it is a square in the local
completion.  The existing Kummer tensor-norm theorem then makes the local
norm subgroup all of the completion units, so the actual infinite-place
Artin automorphism and its Kummer root character are trivial.
-/

open scoped Classical NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open KummerTheory

variable (K : Type) [Field K] [NumberField K]

/-- In the quadratic real case, a positive radicand makes the infinite-place
Kummer root character trivial. -/
theorem infinitePlaceKummerRootCharacter_eq_one_of_real_of_radical_pos
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : InfinitePlace K) (a b : Kˣ)
    (hn : (n : ℕ) = 2) (hv : v.IsReal)
    (hb : 0 < InfinitePlace.embedding_of_isReal hv (b : K)) :
    infinitePlaceKummerRootCharacter K n hnK hmu v a b = 1 := by
  let L := chosenSimpleKummerExtension K n hnK b
  let : FiniteDimensional K L :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let : IsAbelianGalois K L :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let : NumberField L := NumberField.of_module_finite K L
  let a_v : v.Completionˣ :=
    Units.map (algebraMap K v.Completion).toMonoidHom a
  have hbSquare :
      Units.map (algebraMap K v.Completion).toMonoidHom b ∈
        (powMonoidHom (n : ℕ) : v.Completionˣ →* v.Completionˣ).range := by
    rw [hn]
    exact realInfinitePlace_globalUnit_mem_squareSubgroup_of_pos K v hv b hb
  have hNormTop :
      infiniteTensorNormSubgroup (K := K) (L := L) v = ⊤ := by
    simpa only [L] using
      chosenSimpleKummerExtension_infiniteTensorNormSubgroup_eq_top_of_mem_nthPowerSubgroup
        (K := K) n hnK hmu b v hbSquare
  have haNorm :
      a_v ∈ infiniteTensorNormSubgroup (K := K) (L := L) v := by
    rw [hNormTop]
    trivial
  have haKer :
      a_v ∈ (chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v).ker := by
    rw [chosenInfinitePlaceArtinMonoidHom_ker]
    exact haNorm
  have hArtin :
      chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v a_v = 1 :=
    MonoidHom.mem_ker.mp haKer
  change
    (nthRootsSubgroupEquivOfPrimitiveRoots K L n hmu).symm
        (chosenSimpleKummerRootCharacter K n hnK hmu b
          (chosenInfinitePlaceArtinMonoidHom
            (K := K) (L := L) v a_v)) = 1
  rw [hArtin, map_one, map_one]

/-- The explicit real Hilbert factor and the Kummer root character agree
when the quadratic radicand is positive. -/
theorem infinitePlaceKummerRootCharacter_localGlobal_of_real_of_radical_pos
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : InfinitePlace K) (a b : Kˣ)
    (hn : (n : ℕ) = 2) (hv : v.IsReal)
    (hb : 0 < InfinitePlace.embedding_of_isReal hv (b : K)) :
    infinitePlaceKummerRootCharacter K n hnK hmu v a b =
      infinitePlaceHilbertSymbol K n v a b := by
  rw [infinitePlaceKummerRootCharacter_eq_one_of_real_of_radical_pos
    K n hnK hmu v a b hn hv hb]
  have hbNotNeg :
      ¬InfinitePlace.embedding_of_isReal hv (b : K) < 0 :=
    not_lt_of_ge hb.le
  symm
  apply Subtype.ext
  simp [infinitePlaceHilbertSymbol, hn, hv, hbNotNeg]

end Reciprocity
end GlobalClassFieldTheory
