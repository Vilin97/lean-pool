/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.GlobalCompositumValuationInertiaBound
import LeanPool.ClassFieldTheory.ClassFieldTheory.RamificationTheory.HilbertRamification.Dedekind.PadicValuationInertia
import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.UnramifiedCompositumSupport
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.DegreeFromChosenPrimes
/-!
# Global Kronecker--Weber

The synchronized prime above each member of the finite ramification support
has inertia cardinality at most the corresponding prime-power totient.
Outside that support the auxiliary compositum is unramified.  The finite
inertia groups therefore generate its full abelian Galois group, and their
product bounds its degree by the degree of the conductor cyclotomic field.
-/

noncomputable section

namespace KroneckerWeber

open NumberField
open AlgebraicNumberTheory
open AlgebraicNumberTheory.Ramification
open HilbertRamification.Dedekind
open scoped NumberField

variable (L : Type) [Field L]
variable [hNF : NumberField L] [hLab : IsAbelianGalois ℚ L]

/-- The global degree estimate which completes the arithmetic part of the
Kronecker–Weber argument. -/
theorem kroneckerWeberCompositum_finrank_le_totient :
    Module.finrank ℚ (kroneckerWeberCompositumField L) ≤
      Nat.totient (kroneckerWeberConductorCandidate (L := L)) := by
  classical
  let M := kroneckerWeberCompositumField L
  let C := CyclotomicField (kroneckerWeberConductorCandidate (L := L)) ℚ
  let S := kroneckerWeberRamifiedPrimes (L := L)
  let e : Nat.Primes → ℕ :=
    kroneckerWeberLocalRamificationExponent (L := L)
  let A : IntermediateField ℚ M :=
    kroneckerWeberCompositumLeftField (L := L)
  let B : IntermediateField ℚ M :=
    (kroneckerWeberCompositumEmbeddingRight (L := L)).fieldRange
  let eLA : L ≃ₐ[ℚ] A :=
    kroneckerWeberCompositumLeftEquiv (L := L)
  let eCB : C ≃ₐ[ℚ] B :=
    AlgEquiv.ofInjectiveField
      (kroneckerWeberCompositumEmbeddingRight (L := L))
  let _ : IsAbelianGalois ℚ A :=
    IsAbelianGalois.of_algHom eLA.symm.toAlgHom
  let _ : IsAbelianGalois ℚ B :=
    IsAbelianGalois.of_algHom eCB.symm.toAlgHom
  have hsup : A ⊔ B = ⊤ := by
    change
      (finiteAbelianCompositumEmbeddingLeft ℚ L
          (CyclotomicField
            (kroneckerWeberConductorCandidate (L := L)) ℚ)).fieldRange ⊔
        (finiteAbelianCompositumEmbeddingRight ℚ L
          (CyclotomicField
            (kroneckerWeberConductorCandidate (L := L)) ℚ)).fieldRange = ⊤
    exact finiteAbelianCompositum_embeddingRanges_sup_eq_top
      ℚ L
        (CyclotomicField
          (kroneckerWeberConductorCandidate (L := L)) ℚ)
  let chosen : ∀ p : Nat.Primes,
      Ideal.primesOver (rationalPrimeIdeal p) (𝓞 M) := fun p ↦
    if hp : p ∈ S then
      letI : Fact p.1.Prime := ⟨p.2⟩
      let wM :=
        kroneckerWeberGlobalCompositumCyclotomicPadicExtension
          (L := L) p hp
      have hpPrime : (⟨p.1, Fact.out⟩ : Nat.Primes) = p :=
        Subtype.ext rfl
      ⟨globalPadicPrimeIdeal p.1 M wM,
        globalPadicPrimeIdeal_isPrime p.1 M wM,
        by simpa only [hpPrime] using globalPadicPrimeIdeal_liesOver p.1 M wM⟩
    else
      kroneckerWeberCompositumPrimeAbove (L := L) p
  have hunramifiedOutside :
      ∀ (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.IsMaximal],
        (¬ ∃ p ∈ S, rationalPrimeIdeal p = Q.under ℤ) →
          Algebra.IsUnramifiedAt ℤ Q := by
    intro Q _ _ hQ
    exact kroneckerWeberCompositum_isUnramifiedAt_of_not_mem
      (L := L) A B eLA eCB hsup Q hQ
  have hcard : ∀ p ∈ S,
      Nat.card
          (inertiaGroup (chosen p).1 (M ≃ₐ[ℚ] M)) ≤
        Nat.totient (p.1 ^ e p) := by
    intro p hp
    let _ : Fact p.1.Prime := ⟨p.2⟩
    let wM :=
      kroneckerWeberGlobalCompositumCyclotomicPadicExtension
        (L := L) p hp
    have hchosen :
        (chosen p).1 = globalPadicPrimeIdeal p.1 M wM := by
      simp only [chosen, dite_eq_left hp]
      congr 1
    rw [hchosen]
    have hbridge :=
      globalPadicPrimeIdeal_inertia_natCard_le_valuationInertia p.1 M wM
    have hlocal :=
      kroneckerWeberGlobalCompositumValuationInertiaCard_le
        (L := L) p hp
    rw [kroneckerWeberGlobalCompositumValuationInertiaCard] at hlocal
    exact hbridge.trans hlocal
  have hdegree :=
    finrank_le_totient_prod_primePowers_of_chosen_primes
      M S e chosen hunramifiedOutside hcard
  simpa [M, S, e, kroneckerWeberConductorCandidate] using hdegree

/-- The actual embedding into the cyclotomic field whose order is the
conductor candidate assembled from the finitely many ramified primes. -/
noncomputable def kroneckerWeberCyclotomicEmbedding :
    L →ₐ[ℚ]
      CyclotomicField (kroneckerWeberConductorCandidate (L := L)) ℚ :=
  kroneckerWeberEmbeddingOfCompositumFinrankLe
    (L := L) (kroneckerWeberCompositum_finrank_le_totient (L := L))

end KroneckerWeber

end
