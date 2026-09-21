/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.BarredPermutation
/-!
# Prime shuffle coefficients in the Fox--Neuwirth boundary

Merging two consecutive blocks of sizes `k` and `p-k` produces one contribution for every
order-preserving shuffle of the two blocks.  The number of such shuffles is `p.choose k`.  For a
prime `p` and `0 < k < p`, this coefficient is divisible by `p`; this is the arithmetic reason the
sum of the top dual cells is a cycle modulo `p`.
-/

namespace NRR

variable {p k : ℕ}

namespace FoxNeuwirth


/-- A shuffle is encoded by the positions occupied by the first block. -/
def ShuffleIndex (p k : ℕ) :=
  {s : Finset (Fin p) // s.card = k}

namespace ShuffleIndex

noncomputable instance : Fintype (ShuffleIndex p k) := by
  unfold ShuffleIndex
  infer_instance
noncomputable instance : DecidableEq (ShuffleIndex p k) := Classical.decEq _

@[simp] theorem card (p k : ℕ) :
    Fintype.card (ShuffleIndex p k) = p.choose k := by
  change Fintype.card {s : Finset (Fin p) // s.card = k} = p.choose k
  simpa using (Fintype.card_finset_len (α := Fin p) k)

end ShuffleIndex

/-- Number of order-preserving shuffles of blocks of sizes `k` and `p-k`. -/
def shuffleMultiplicity (p k : ℕ) : ℕ := p.choose k

@[simp] theorem card_shuffleIndex :
    Fintype.card (ShuffleIndex p k) = shuffleMultiplicity p k := by
  simp [shuffleMultiplicity]

@[simp] theorem shuffleMultiplicity_zero (p : ℕ) :
    shuffleMultiplicity p 0 = 1 := by
  simp [shuffleMultiplicity]

@[simp] theorem shuffleMultiplicity_self (p : ℕ) :
    shuffleMultiplicity p p = 1 := by
  simp [shuffleMultiplicity]

 theorem prime_dvd_shuffleMultiplicity
    (hp : Nat.Prime p) (hk0 : 0 < k) (hkp : k < p) :
    p ∣ shuffleMultiplicity p k := by
  unfold shuffleMultiplicity
  exact hp.dvd_choose hkp (by omega) le_rfl

 theorem shuffleMultiplicity_mod_prime_eq_zero
    (hp : Nat.Prime p) (hk0 : 0 < k) (hkp : k < p) :
    shuffleMultiplicity p k % p = 0 := by
  exact Nat.mod_eq_zero_of_dvd (prime_dvd_shuffleMultiplicity hp hk0 hkp)

/-- The unsigned codimension-one boundary coefficient for a split into nonempty blocks. -/
def unsignedFacetCoefficient (p leftSize : ℕ) : ℤ :=
  (shuffleMultiplicity p leftSize : ℤ)

 theorem prime_dvd_unsignedFacetCoefficient
    (hp : Nat.Prime p) (hk0 : 0 < k) (hkp : k < p) :
    (p : ℤ) ∣ unsignedFacetCoefficient p k := by
  exact Nat.cast_dvd_cast (prime_dvd_shuffleMultiplicity hp hk0 hkp)

end FoxNeuwirth

end NRR
