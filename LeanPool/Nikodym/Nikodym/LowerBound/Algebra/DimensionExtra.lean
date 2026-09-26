/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module


public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Dimension
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Interface

/-!
# Dimension of a quotient through its primes

This file implements blueprint node **D01** of the algebra backend: the Krull dimension of `R ⧸ J`
is bounded by the dimensions of the quotients `R ⧸ p` over the primes `p ⊇ J`.

* `ringKrullDim_quotient_le_of_forall_isPrime`: if `ringKrullDim (R ⧸ p) ≤ n` for every prime
  `p ⊇ J`, then `ringKrullDim (R ⧸ J) ≤ n`.
* `quotDim_le_of_forall_isPrime`: the same for `quotDim` on `MvPolynomial (Fin d) K`, for a proper
  ideal `J`.
-/

@[expose] public section

namespace Nikodym.LowerBound

open Ideal

section General

variable {R : Type*} [CommRing R]

/-- Blueprint D01: **the dimension of `R ⧸ J` is controlled by the primes over `J`.** A chain of
primes containing `J` starts at some prime `p ⊇ J`, and is a chain of primes containing `p`, so
its length is at most `ringKrullDim (R ⧸ p)`. -/
theorem ringKrullDim_quotient_le_of_forall_isPrime (J : Ideal R) (n : ℕ)
    (h : ∀ p : Ideal R, p.IsPrime → J ≤ p → ringKrullDim (R ⧸ p) ≤ n) :
    ringKrullDim (R ⧸ J) ≤ n := by
  rw [ringKrullDim_quotient, Order.krullDim]
  refine iSup_le fun l ↦ ?_
  set p : Ideal R := l.head.1.asIdeal with hp
  have hJp : J ≤ p := (PrimeSpectrum.mem_zeroLocus _ _).mp l.head.2
  have hl : ∀ i, (l i).1 ∈ PrimeSpectrum.zeroLocus (R := R) p := fun i ↦
    (PrimeSpectrum.mem_zeroLocus _ _).mpr
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr (Subtype.coe_le_coe.mpr (l.head_le i)))
  let l' : LTSeries (PrimeSpectrum.zeroLocus (R := R) p) :=
    { length := l.length
      toFun := fun i ↦ ⟨(l i).1, hl i⟩
      step := fun i ↦ show (l i.castSucc).1 < (l i.succ).1 from l.step i }
  calc ((l.length : ℕ∞) : WithBot ℕ∞) = l'.length := rfl
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := R) p) :=
        Order.LTSeries.length_le_krullDim l'
    _ = ringKrullDim (R ⧸ p) := (ringKrullDim_quotient p).symm
    _ ≤ n := h p l.head.1.2 hJp

end General

section QuotDim

variable {K : Type*} [Field K] {d : ℕ}

/-- Blueprint D01: **`quotDim` is controlled by the primes over `J`.** For a proper ideal `J` of
`MvPolynomial (Fin d) K`, if `quotDim p ≤ n` for every prime `p ⊇ J`, then `quotDim J ≤ n`. -/
theorem quotDim_le_of_forall_isPrime {J : Ideal (MvPolynomial (Fin d) K)} {n : ℕ}
    (h : ∀ p : Ideal (MvPolynomial (Fin d) K), p.IsPrime → J ≤ p → quotDim p ≤ n) (hJ : J ≠ ⊤) :
    quotDim J ≤ n := by
  have h' := ringKrullDim_quotient_le_of_forall_isPrime J n fun p hp hJp ↦ by
    rw [← coe_quotDim p hp.ne_top]
    exact_mod_cast h p hp hJp
  rw [← coe_quotDim J hJ] at h'
  exact_mod_cast h'

/-- Blueprint A01 (6) in terms of `quotDim`: a minimal prime `J` over `I + (g)`, for `I` prime and
`g ∉ I`, has `quotDim J + 1 = quotDim I`. -/
theorem quotDim_add_one_of_mem_minimalPrimes_sup {I : Ideal (MvPolynomial (Fin d) K)} [I.IsPrime]
    {g : MvPolynomial (Fin d) K} (hg : g ∉ I) {J : Ideal (MvPolynomial (Fin d) K)}
    (hJ : J ∈ (I ⊔ Ideal.span {g}).minimalPrimes) : quotDim J + 1 = quotDim I := by
  have h := ringKrullDim_quotient_add_one_of_mem_minimalPrimes_sup K I hg hJ
  rw [← coe_quotDim J hJ.1.1.ne_top, ← coe_quotDim I Ideal.IsPrime.ne_top'] at h
  exact_mod_cast h

end QuotDim

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
