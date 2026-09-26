/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.RationalPrime
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Conjugation
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.NumberFieldPrimes
/-!
# Global cyclotomic inertia argument: coverage by finitely many chosen inertia groups

For an abelian Galois extension of `ℚ`, all primes above one rational prime
have the same inertia group: primes above the same rational prime are conjugate, and conjugation is
trivial in an abelian group.  Consequently, if the extension is unramified
outside a finite set `S`, one chosen prime above each member of `S` supplies
all nontrivial inertia groups.
-/

@[expose] public section

noncomputable
section

namespace HilbertRamification.Dedekind

open NumberField
open scoped NumberField
open AlgebraicNumberTheory.Ramification

attribute [local instance] Ideal.Quotient.field

/-- In an abelian Galois extension, primes above the same base prime have
equal inertia groups. -/
theorem inertiaGroup_eq_of_liesOver_of_commGroup
    {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [CommGroup G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B]
    (p : Ideal A) (P Q : Ideal B)
    [P.IsPrime] [P.LiesOver p] [Q.IsPrime] [Q.LiesOver p] :
    inertiaGroup P G = inertiaGroup Q G := by
  obtain ⟨σ, rfl⟩ :=
    exists_smul_eq_of_isGaloisGroup (A := A) (B := B) p P Q G
  ext τ
  rw [mem_inertiaGroup_smul_iff]
  simp [mul_comm]

variable {G M : Type*}
variable [CommGroup G]
variable [Field M] [NumberField M]
variable [MulSemiringAction G M]
variable [IsGaloisGroup G ℚ M]

/-- The global cyclotomic inertia argument, chosen-prime inertia coverage.

Let `S` be a finite set of rational primes and choose one prime of `M` above
each rational prime.  If every finite prime whose contraction is outside `S`
is unramified over `ℤ`, then every finite-prime inertia group is contained in
the supremum of the inertia groups at the chosen primes in `S`.

The choice is represented by an element of `Ideal.primesOver`, so its
primality and lies-over property are concrete data rather than assumptions. -/
theorem inertiaGroup_le_finsetSup_chosen_of_unramified_outside
    (S : Finset Nat.Primes)
    (chosen : ∀ p : Nat.Primes,
      Ideal.primesOver (rationalPrimeIdeal p) (𝓞 M))
    (hunramifiedOutside :
      ∀ (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.IsMaximal],
        (¬ ∃ p ∈ S, rationalPrimeIdeal p = Q.under ℤ) →
          Algebra.IsUnramifiedAt ℤ Q) :
    ∀ (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.IsMaximal],
      inertiaGroup Q G ≤
        S.sup (fun p => inertiaGroup (chosen p).1 G) := by
  let : Finite G := IsGaloisGroup.finite G ℚ M
  intro Q _ _
  let q : Ideal ℤ := Q.under ℤ
  let : Q.LiesOver q := ⟨rfl⟩
  by_cases hqS : ∃ p ∈ S, rationalPrimeIdeal p = q
  · obtain ⟨p, hpS, hpq⟩ := hqS
    let P : Ideal (𝓞 M) := (chosen p).1
    let : P.IsPrime := (chosen p).2.1
    let : P.LiesOver (rationalPrimeIdeal p) := (chosen p).2.2
    let : Q.LiesOver (rationalPrimeIdeal p) := ⟨hpq⟩
    have hIQ : inertiaGroup Q G = inertiaGroup P G :=
      (inertiaGroup_eq_of_liesOver_of_commGroup
        (rationalPrimeIdeal p) P Q).symm
    rw [hIQ]
    exact Finset.le_sup
      (f := fun r => inertiaGroup (chosen r).1 G) hpS
  · have hunramified : Algebra.IsUnramifiedAt ℤ Q :=
      hunramifiedOutside Q hqS
    let : Algebra.IsUnramifiedAt ℤ Q := hunramified
    have hunramified_ringOfIntegers :
        Algebra.IsUnramifiedAt (𝓞 ℚ) Q :=
      Algebra.IsUnramifiedAt.of_restrictScalars ℤ Q
    let : Finite
        ((𝓞 ℚ) ⧸ basePrime (K := ℚ) Q) :=
      inferInstance
    let : PerfectField
        ((𝓞 ℚ) ⧸ basePrime (K := ℚ) Q) :=
      PerfectField.ofFinite
    let : Algebra.IsSeparable
        ((𝓞 ℚ) ⧸ basePrime (K := ℚ) Q) ((𝓞 M) ⧸ Q) :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    have hbot : inertiaGroup Q G = ⊥ :=
      (inertiaGroup_eq_bot_iff_isUnramifiedAt
        (K := ℚ) (L := M) (G := G) (P := Q)).2
        hunramified_ringOfIntegers
    rw [hbot]
    exact bot_le

end HilbertRamification.Dedekind

end
