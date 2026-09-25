/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NormalClosure
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.NormalClosure
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.PrimeOrderFixedField
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.CyclicPrimePowerFullDecomposition
/-!
# Cofinitely split finite extensions are trivial

For a finite extension of number fields `L / K`, if all but finitely
many finite places of `K` split completely in `L`, then `L / K` has
degree one.  The normal-closure and splitting-transport constructions
used in the proof live in their general algebraic-number-theory
modules; this file contains only the global class-field-theoretic
conclusion.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Cohomology

variable
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

open scoped Classical in
/-- If all but finitely many finite places of `K` split completely in
the finite extension `L / K`, then the extension has degree one.

The proof passes to the finite normal closure `M`.  If `M / K` were
nontrivial, a prime-order automorphism would give an intermediate field
`K'` for which `M / K'` is cyclic of prime degree.  The infinitude of
full-decomposition places in cyclic prime-degree extensions then supplies
infinitely many nonsplitting places of `K'`, contradicting the finiteness
transported from `M / K`. -/
theorem finrank_eq_one_of_finite_nonSplittingPlaces
    (hfinite :
      {v : HeightOneSpectrum (𝓞 K) |
        ¬ FinitePlaceSplitsCompletelyInExtension
          (K := K) (E := L) v}.Finite) :
    Module.finrank K L = 1 := by
  let M := finiteNormalClosure K L
  let : NumberField M :=
    finiteNormalClosure_numberField K L
  let : IsGalois K M :=
    finiteNormalClosure_isGalois K L
  have hfiniteM :
      {v : HeightOneSpectrum (𝓞 K) |
        ¬ FinitePlaceSplitsCompletely
          (K := K) (L := M) v}.Finite := by
    simpa only [M] using
      finite_nonSplittingPlaces_normalClosure_of_original
        K L hfinite
  have hdegreeM : Module.finrank K M = 1 := by
    by_contra hne
    have hgt : 1 < Module.finrank K M := by
      have hpos : 0 < Module.finrank K M :=
        Module.finrank_pos
      omega
    let K' :=
      primeOrderFixedField
        (K := K) (L := M) hgt
    let p :=
      fixedFieldPrime
        (K := K) (L := M) hgt
    have hp : p.Prime := by
      simpa only [p] using
        fixedFieldPrime_prime
          (K := K) (L := M) hgt
    have hrelativeDegree :
        Module.finrank K' M = p := by
      simpa only [K', p] using
        primeOrderFixedField_finrank
          (K := K) (L := M) hgt
    have hrelativeNontrivial :
        1 < Module.finrank K' M := by
      rw [hrelativeDegree]
      exact hp.one_lt
    have hcard :
        Nat.card (M ≃ₐ[K'] M) = p ^ 1 := by
      calc
        Nat.card (M ≃ₐ[K'] M) = p := by
          simpa only [K', p] using
            primeOrderFixedField_card_aut
              (K := K) (L := M) hgt
        _ = p ^ 1 := by simp
    have hinfinite :
        Set.Infinite
          {v : HeightOneSpectrum (𝓞 K') |
            finitePlaceDecompositionGroup
                (K := K') (L := M) v = ⊤} :=
      cyclic_prime_power_infinite_fullDecompositionPlaces
        (K := K') (L := M)
        hp (by omega) hcard
    have hfiniteRelative :
        {v : HeightOneSpectrum (𝓞 K') |
          ¬ FinitePlaceSplitsCompletely
            (K := K') (L := M) v}.Finite :=
      finite_nonsplittingPlaces_over_intermediate
        (K := K) (M := K') (L := M) hfiniteM
    apply hinfinite
    apply hfiniteRelative.subset
    intro v hv
    exact
      finitePlace_not_splitsCompletely_of_decompositionGroup_eq_top
        (K := K') (L := M)
        hrelativeNontrivial v hv
  have hle :
      Module.finrank K L ≤ Module.finrank K M := by
    simpa only [M] using finrank_le_finiteNormalClosure K L
  have hpos : 0 < Module.finrank K L :=
    Module.finrank_pos
  omega

open scoped Classical in
/-- Algebra-equivalence form of the degree-one conclusion, expressing
that `L` is the base field without identifying the two Lean types
definitionally. -/
noncomputable def algEquivBaseOfFiniteNonSplittingPlaces
    (hfinite :
      {v : HeightOneSpectrum (𝓞 K) |
        ¬ FinitePlaceSplitsCompletelyInExtension
          (K := K) (E := L) v}.Finite) :
    L ≃ₐ[K] K :=
  algEquivBaseOfFinrankEqOne K L
    (finrank_eq_one_of_finite_nonSplittingPlaces K L hfinite)

end Cohomology
end GlobalClassFieldTheory
