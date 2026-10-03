/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.InfinitePlacePositive
/-!
# Ramification of a negative quadratic Kummer radical at a real place
-/

@[expose] public section

open scoped NumberField
open NumberField

noncomputable
section

namespace GlobalClassFieldTheory
namespace Reciprocity

open KummerTheory

variable (K : Type) [Field K] [NumberField K]

omit [NumberField K] in
open scoped Classical in
/-- In the quadratic Kummer extension of a radicand that is negative at a
real place, the chosen infinite place upstairs is ramified. -/
theorem chosenSimpleKummerExtension_chosenInfinitePlace_isRamified_of_real_of_radical_neg
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : InfinitePlace K) (b : Kˣ)
    (hn : (n : ℕ) = 2) (hv : v.IsReal)
    (hb : InfinitePlace.embedding_of_isReal hv (b : K) < 0) :
    let L := chosenSimpleKummerExtension K n hnK b
    letI : FiniteDimensional K L :=
      chosenSimpleKummerExtension_finiteDimensional K n hnK b
    letI : IsAbelianGalois K L :=
      chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
    letI : NumberField L := NumberField.of_module_finite K L
    (chosenInfinitePlaceAbove (L := L) v).IsRamified K := by
  let L := chosenSimpleKummerExtension K n hnK b
  let : FiniteDimensional K L :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let : IsAbelianGalois K L :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let beta : L :=
    (chosenSimpleKummerRootUnit K n hnK b : Lˣ)
  have hbeta : beta ^ 2 = algebraMap K L (b : K) := by
    have hunit := congrArg Units.val
      (chosenSimpleKummerRootUnit_pow K n hnK b)
    rw [hn] at hunit
    exact hunit
  let w := chosenInfinitePlaceAbove (L := L) v
  have hw : w.comap (algebraMap K L) = v :=
    chosenInfinitePlaceAbove_comap (L := L) v
  have hwComplex : w.IsComplex := by
    apply InfinitePlace.not_isReal_iff_isComplex.mp
    intro hwReal
    have hcomapReal : (w.comap (algebraMap K L)).IsReal := by
      rw [hw]
      exact hv
    have hcomplexComp :=
      InfinitePlace.comap_embedding_of_isReal
        (algebraMap K L) hcomapReal
    have hrealComp :
        (InfinitePlace.embedding_of_isReal hwReal).comp
            (algebraMap K L) =
          InfinitePlace.embedding_of_isReal hv := by
      apply RingHom.ext
      intro x
      apply Complex.ofReal_injective
      change
        ((InfinitePlace.embedding_of_isReal hwReal
          (algebraMap K L x) : ℝ) : ℂ) =
          ((InfinitePlace.embedding_of_isReal hv x : ℝ) : ℂ)
      rw [InfinitePlace.embedding_of_isReal_apply,
        InfinitePlace.embedding_of_isReal_apply]
      rw [← RingHom.comp_apply, ← hcomplexComp, hw]
    have hsq :
        (InfinitePlace.embedding_of_isReal hwReal beta) ^ 2 =
          InfinitePlace.embedding_of_isReal hv (b : K) := by
      calc
        (InfinitePlace.embedding_of_isReal hwReal beta) ^ 2 =
            InfinitePlace.embedding_of_isReal hwReal (beta ^ 2) := by
          rw [map_pow]
        _ = InfinitePlace.embedding_of_isReal hwReal
            (algebraMap K L (b : K)) := by rw [hbeta]
        _ = InfinitePlace.embedding_of_isReal hv (b : K) := by
          exact DFunLike.congr_fun hrealComp (b : K)
    nlinarith [sq_nonneg
      (InfinitePlace.embedding_of_isReal hwReal beta)]
  apply InfinitePlace.isRamified_iff.mpr
  exact ⟨hwComplex, by rw [hw]; exact hv⟩

end Reciprocity
end GlobalClassFieldTheory
