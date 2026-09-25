/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.GlobalCompositumLeftFactors
/-!
# The global cyclotomic factor inside the common local target

The global conductor cyclotomic field embeds, after base change and enlargement
of the order, into the common `p`-adic cyclotomic target used by the synchronized
valued compositum construction.
-/

@[expose] public section

noncomputable section

namespace KroneckerWeber

open AlgebraicNumberTheory
open AlgebraicNumberTheory.Valuations

variable (L : Type) [Field L]
variable [hNF : NumberField L] [hLab : IsAbelianGalois ℚ L]

/-- The global conductor cyclotomic factor embedded after base change to
`ℚ_p` and enlargement of the cyclotomic order. -/
noncomputable def kroneckerWeberGlobalRightEmbeddingProperty
    (p : Nat.Primes) : Prop := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  exact Nonempty
    (CyclotomicField (kroneckerWeberConductorCandidate (L := L)) ℚ →ₐ[ℚ]
      CyclotomicField (kroneckerWeberLocalCompositumOrder (L := L) p)
        ℚ_[p.1])

/-- At a ramified prime, the global conductor cyclotomic field embeds into
the common local cyclotomic target. -/
theorem kroneckerWeberGlobalRightEmbedding
    (p : Nat.Primes)
    (hp : p ∈ kroneckerWeberRamifiedPrimes (L := L)) :
    kroneckerWeberGlobalRightEmbeddingProperty (L := L) p := by
  let : Fact p.1.Prime := ⟨p.2⟩
  exact ⟨cyclotomicFieldEmbeddingOfBaseAndDvd ℚ ℚ_[p.1]
    (kroneckerWeberConductorCandidate (L := L))
    (kroneckerWeberLocalCompositumOrder (L := L) p)
    (kroneckerWeberConductorCandidate_pos (L := L))
    (kroneckerWeberLocalCompositumOrder_pos (L := L) p)
    (kroneckerWeberConductorCandidate_dvd_localCompositumOrder
      (L := L) p hp)⟩

end KroneckerWeber

end
