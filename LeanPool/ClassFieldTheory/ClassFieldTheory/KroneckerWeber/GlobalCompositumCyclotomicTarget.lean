/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.Setup
/-!
# The common local cyclotomic target

At a ramified prime `p`, the structured local embedding of `L` has order
`(p^f - 1) * p^e`, while the global conductor has order `p^e * c` with
`c` prime to `p`.  Their common target has order
`((p^f - 1) * c) * p^e`; crucially, it uses the same exponent `e`.
-/

@[expose] public section

noncomputable
section

namespace KroneckerWeber

variable (L : Type) [Field L]
variable [hNF : NumberField L] [hLab : IsAbelianGalois ℚ L]

/-- The prime-to-`p` factor of the common local target. -/
noncomputable def kroneckerWeberLocalCompositumCoprimePart
    (p : Nat.Primes) : ℕ :=
  (p.1 ^ kroneckerWeberLocalUnramifiedDegree (L := L) p - 1) *
    kroneckerWeberConductorCoprimePart (L := L) p

/-- The common local cyclotomic order, retaining exactly the conductor
exponent chosen at `p`. -/
noncomputable def kroneckerWeberLocalCompositumOrder
    (p : Nat.Primes) : ℕ :=
  kroneckerWeberLocalCompositumCoprimePart (L := L) p *
    p.1 ^ kroneckerWeberLocalRamificationExponent (L := L) p

/-- The prime-to-`p` part of the common local target is coprime to `p`. -/
theorem kroneckerWeberLocalCompositumCoprimePart_coprime
    (p : Nat.Primes) :
    Nat.Coprime p.1
      (kroneckerWeberLocalCompositumCoprimePart (L := L) p) := by
  let : Fact p.1.Prime := ⟨p.2⟩
  rw [kroneckerWeberLocalCompositumCoprimePart]
  have hprimeTo : Nat.Coprime p.1
      (p.1 ^ kroneckerWeberLocalUnramifiedDegree (L := L) p - 1) := by
    rw [p.2.coprime_iff_not_dvd]
    intro hdiv
    have hpow : p.1 ∣
        p.1 ^ kroneckerWeberLocalUnramifiedDegree (L := L) p :=
      dvd_pow_self p.1
        (kroneckerWeberLocalUnramifiedDegree_pos (L := L) p).ne'
    have hpowgt : 1 <
        p.1 ^ kroneckerWeberLocalUnramifiedDegree (L := L) p :=
      one_lt_pow₀ p.2.one_lt
        (kroneckerWeberLocalUnramifiedDegree_pos (L := L) p).ne'
    have hdiff :
        p.1 ^ kroneckerWeberLocalUnramifiedDegree (L := L) p -
            (p.1 ^ kroneckerWeberLocalUnramifiedDegree (L := L) p - 1) =
          1 := by
      omega
    have hone : p.1 ∣ 1 := by
      rw [← hdiff]
      exact Nat.dvd_sub hpow hdiv
    exact p.2.ne_one (Nat.dvd_one.mp hone)
  exact hprimeTo.mul_right
    (kroneckerWeberConductorCoprimePart_coprime (L := L) p)

/-- The common local cyclotomic order is positive. -/
theorem kroneckerWeberLocalCompositumOrder_pos
    (p : Nat.Primes) :
    0 < kroneckerWeberLocalCompositumOrder (L := L) p := by
  rw [kroneckerWeberLocalCompositumOrder,
    kroneckerWeberLocalCompositumCoprimePart]
  apply Nat.mul_pos
  · apply Nat.mul_pos
    · exact Nat.sub_pos_of_lt
        (one_lt_pow₀ p.2.one_lt
          (kroneckerWeberLocalUnramifiedDegree_pos (L := L) p).ne')
    · rw [kroneckerWeberConductorCoprimePart]
      exact Finset.prod_pos fun q _ ↦ pow_pos q.2.pos _
  · exact pow_pos p.2.pos _

/-- The structured local cyclotomic order divides the common local order. -/
theorem kroneckerWeberLocalStructuredOrder_dvd_compositumOrder
    (p : Nat.Primes) :
    (p.1 ^ kroneckerWeberLocalUnramifiedDegree (L := L) p - 1) *
        p.1 ^ kroneckerWeberLocalRamificationExponent (L := L) p ∣
      kroneckerWeberLocalCompositumOrder (L := L) p := by
  refine ⟨kroneckerWeberConductorCoprimePart (L := L) p, ?_⟩
  rw [kroneckerWeberLocalCompositumOrder,
    kroneckerWeberLocalCompositumCoprimePart]
  ac_rfl

/-- At a ramified prime, the global conductor candidate divides the common
local cyclotomic order. -/
theorem kroneckerWeberConductorCandidate_dvd_localCompositumOrder
    (p : Nat.Primes)
    (hp : p ∈ kroneckerWeberRamifiedPrimes (L := L)) :
    kroneckerWeberConductorCandidate (L := L) ∣
      kroneckerWeberLocalCompositumOrder (L := L) p := by
  rw [kroneckerWeberConductorCandidate_eq_primePower_mul_coprimePart
    (L := L) p hp]
  refine ⟨p.1 ^ kroneckerWeberLocalUnramifiedDegree (L := L) p - 1, ?_⟩
  rw [kroneckerWeberLocalCompositumOrder,
    kroneckerWeberLocalCompositumCoprimePart]
  ac_rfl

end KroneckerWeber

end
