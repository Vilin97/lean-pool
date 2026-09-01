/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Nullstellensatz.RadicalReduction

/-!
# Cancellation on a prime analytic zero set

The generic-fiber proof repeatedly clears a denominator `D` which is not in
the contracted prime.  If `D * c` vanishes on that prime's local zero set,
the lower-dimensional prime theorem puts the product in the prime, and
primality cancels `D`.
-/


namespace LocalComplexGeometry

noncomputable section

/-- Cancel a nonmember from a product in a prime ideal. -/
theorem mem_prime_of_mul_mem_of_not_mem {n : ℕ}
    {P : Ideal (HolomorphicGerm n)} (hP : P.IsPrime)
    {D c : HolomorphicGerm n} (hD : D ∉ P) (hDc : D * c ∈ P) :
    c ∈ P := by
  exact (hP.mem_or_mem hDc).resolve_left hD

/-- Prime zero-set cancellation in the exact form used after denominator
clearing. -/
theorem mem_prime_of_mul_vanishes_on_zeroSet
    {n : ℕ} (hprime : PrimeZeroSetProperty n)
    (P : Ideal (HolomorphicGerm n)) (hP : P.IsPrime)
    {D c : HolomorphicGerm n} (hD : D ∉ P)
    (hvanish : idealZeroSetGerm P ≤ germZeroLocus (D * c)) :
    c ∈ P := by
  have hDcVanishing : D * c ∈ vanishingIdeal (idealZeroSetGerm P) := hvanish
  have hDc : D * c ∈ P := by
    rw [← hprime P hP]
    exact hDcVanishing
  exact mem_prime_of_mul_mem_of_not_mem hP hD hDc

/-- A finite product of elements outside a prime remains outside the prime. -/
theorem finset_prod_not_mem_prime {R : Type*} [CommRing R]
    {P : Ideal R} (hP : P.IsPrime) {ι : Type*}
    (S : Finset ι) (f : ι → R)
    (hf : ∀ i ∈ S, f i ∉ P) :
    (∏ i ∈ S, f i) ∉ P := by
  let : P.IsPrime := hP
  change (∏ i ∈ S, f i) ∈ P.primeCompl
  exact Submonoid.prod_mem P.primeCompl fun i hi ↦ hf i hi

end

end LocalComplexGeometry
