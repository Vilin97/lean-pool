/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NumberField.DegreeOnePrimes
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlaceIdeal
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.Algebra.Group.Subgroup.Finite

/-! # Completely Split Primes -/

@[expose] public section
open scoped NumberField Pointwise
open NumberField IsDedekindDomain HilbertRamification.Dedekind

namespace AlgebraicNumberTheory.PrimeSelection

/-- The canonical place of a rational prime is the principal prime ideal
in the actual ring of integers of ℚ. -/
theorem rationalPrimePlace_asIdeal (q : Nat.Primes) :
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm q).asIdeal =
      Ideal.span ({(q.val : 𝓞 ℚ)} : Set (𝓞 ℚ)) := by
  change (Ideal.span ({(q.val : ℤ)} : Set ℤ)).map
    (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm = _
  simp only [Ideal.map_span, Set.image_singleton, map_natCast]

private theorem under_rational_prime_eq_span
    (K : Type*) [Field K] [NumberField K] (q : ℕ)
    (W : HeightOneSpectrum (𝓞 K))
    (hOver : W.asIdeal.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))) :
    W.asIdeal.under (𝓞 ℚ) = Ideal.span ({(q : 𝓞 ℚ)} : Set (𝓞 ℚ)) := by
  have : W.asIdeal.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := hOver
  apply Ideal.comap_injective_of_surjective (algebraMap ℤ (𝓞 ℚ))
    (Rat.int_algebraMap_surjective (𝓞 ℚ))
  change (W.asIdeal.under (𝓞 ℚ)).under ℤ =
    (Ideal.span ({(q : 𝓞 ℚ)} : Set (𝓞 ℚ))).under ℤ
  rw [Ideal.under_under, ← Ideal.over_def W.asIdeal (Ideal.span ({(q : ℤ)} : Set ℤ))]
  have hMap : (Ideal.span ({(q : ℤ)} : Set ℤ)).map (algebraMap ℤ (𝓞 ℚ)) =
      Ideal.span ({(q : 𝓞 ℚ)} : Set (𝓞 ℚ)) := by
    simp only [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [← hMap, Ideal.under_def,
    Ideal.comap_map_of_surjective _ (Rat.int_algebraMap_surjective (𝓞 ℚ)),
    Ideal.comap_bot_of_injective (f := algebraMap ℤ (𝓞 ℚ))
      (Rat.int_algebraMap_injective (𝓞 ℚ)), sup_bot_eq]

/-- A prime above q in a number field lies above the canonical rational
finite place of q. -/
theorem finitePlaceBelow_eq_rationalPrimePlace
    (K : Type*) [Field K] [NumberField K] (q : Nat.Primes)
    (W : HeightOneSpectrum (𝓞 K))
    (hOver : W.asIdeal.LiesOver (Ideal.span ({(q.val : ℤ)} : Set ℤ))) :
    finitePlaceBelow (K := ℚ) W =
      (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm q := by
  apply HeightOneSpectrum.ext
  exact (under_rational_prime_eq_span K q.val W hOver).trans
    (rationalPrimePlace_asIdeal q).symm

/-- For a finite Galois number field, an unramified degree-one prime
has trivial decomposition group, hence gives complete splitting. -/
theorem finitePlaceSplitsCompletely_of_unramified_degree_one
    (K : Type) [Field K] [NumberField K] [IsGalois ℚ K]
    (q : Nat.Primes) (W : HeightOneSpectrum (𝓞 K))
    (hOver : W.asIdeal.LiesOver (Ideal.span ({(q.val : ℤ)} : Set ℤ)))
    (hf : W.asIdeal.inertiaDeg ℤ = 1)
    (hU : Algebra.IsUnramifiedAt ℤ W.asIdeal) :
    FinitePlaceSplitsCompletely (K := ℚ) (L := K)
      ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm q) := by
  have : Fact q.val.Prime := ⟨q.prop⟩
  have : W.asIdeal.LiesOver (Ideal.span ({(q.val : ℤ)} : Set ℤ)) := hOver
  have : Algebra.IsUnramifiedAt ℤ W.asIdeal := hU
  have hq0 : Ideal.span ({(q.val : ℤ)} : Set ℤ) ≠ ⊥ := by
    exact mt Ideal.span_singleton_eq_bot.mp (Int.natCast_ne_zero.mpr q.prop.ne_zero)
  have hCard : Nat.card (decompositionGroup W.asIdeal Gal(K/ℚ)) = 1 := by
    rw [dedekindRamification_decomposition_card_eq_ramificationIdxIn_mul_inertiaDegIn
      (Ideal.span ({(q.val : ℤ)} : Set ℤ)) hq0 W.asIdeal Gal(K/ℚ),
      Ideal.ramificationIdxIn_eq_ramificationIdx
        (Ideal.span ({(q.val : ℤ)} : Set ℤ)) W.asIdeal Gal(K/ℚ),
      Ideal.inertiaDegIn_eq_inertiaDeg
        (Ideal.span ({(q.val : ℤ)} : Set ℤ)) W.asIdeal Gal(K/ℚ),
      Ideal.ramificationIdx_eq_one, hf, one_mul]
  have hBot : decompositionGroup W.asIdeal Gal(K/ℚ) = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ hCard
  rw [finitePlaceSplitsCompletely_iff_stabilizer_eq_bot _ W
    (finitePlaceBelow_eq_rationalPrimePlace K q W hOver)]
  let := finitePlaceMulAction ℚ K
  apply le_antisymm ?_ bot_le
  intro σ hσ
  have hFix : finitePlaceEquiv ℚ K σ W = W := hσ
  have hIdeal := congrArg HeightOneSpectrum.asIdeal hFix
  rw [finitePlaceEquiv_asIdeal] at hIdeal
  have hmem : σ ∈ decompositionGroup W.asIdeal Gal(K/ℚ) := hIdeal
  simpa only [hBot] using hmem

/-- There is a completely split rational prime outside every finite set. -/
theorem exists_completelySplitPrime_not_mem
    (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (bad : Finset ℕ) :
    ∃ q : Nat.Primes, q.val ∉ bad ∧
      FinitePlaceSplitsCompletely (K := ℚ) (L := K)
        ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm q) := by
  obtain ⟨q, hq, hqBad, W, hOver, hf, hU⟩ :=
    exists_unramified_degreeOnePrime_not_mem K bad
  exact ⟨⟨q, hq⟩, hqBad,
    finitePlaceSplitsCompletely_of_unramified_degree_one K ⟨q, hq⟩ W hOver hf hU⟩

end AlgebraicNumberTheory.PrimeSelection
