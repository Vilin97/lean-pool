/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import LeanPool.KasamiCyclicAdditive.MCM.Permutation
import LeanPool.KasamiCyclicAdditive.MCM.ComplementTransport

/-!
# Half-size of the Kasami derivative image

For odd `k`, `mcmMap k` is globally bijective, hence injective on the
Artin--Schreier image.  Since

`derivativeImage k K = image (mcmMap k) (asSet K)`

and `asSet` has exactly half the elements of `K`, the derivative image has half
the field.  For even `k`, coprimality forces `n - k` to be odd, and the
Frobenius transport of `MCM/ComplementTransport.lean` preserves the cardinality of the
derivative image.
-/

open Finset

namespace KasamiCyclicAdditive

noncomputable section

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-- For odd `k`, the Kasami normalized derivative image has exactly half the
field, as a direct consequence of the MCM permutation theorem. -/
theorem kasami_half_size_odd
    {n k : ℕ} (hklt : k < n)
    (hcard : Fintype.card K = 2 ^ n) (hkodd : Odd k) (hkn : Nat.Coprime k n) :
    2 * (derivativeImage k K).card = Fintype.card K := by
  have hbij : Function.Bijective (mcmMap (K := K) k) :=
    mcmMap_bijective_of_odd hklt hcard hkodd hkn
  have himg := derivativeImage_eq_image (K := K) k
  have hcardimg :
      (Finset.image (mcmMap k) (asSet K)).card = (asSet K).card :=
    Finset.card_image_iff.mpr hbij.1.injOn
  rw [himg, hcardimg]
  exact card_asSet (K := K)

/-- With `gcd (k, n) = 1` and `k` even, the complementary parameter `n - k` is
odd. -/
lemma odd_complement_of_even_coprime {n k : ℕ} (hklt : k < n)
    (hkn : Nat.Coprime k n) (hke : Even k) : Odd (n - k) := by
  have hkmod : k % 2 = 0 := Nat.mod_eq_zero_of_dvd hke.two_dvd
  have hn2 : n % 2 = 1 := by
    by_contra hnodd
    have hnmod : n % 2 = 0 := by omega
    have h2n : 2 ∣ n := Nat.dvd_of_mod_eq_zero hnmod
    have h2g : 2 ∣ Nat.gcd k n := Nat.dvd_gcd hke.two_dvd h2n
    rw [hkn] at h2g
    norm_num at h2g
  exact Nat.odd_iff.mpr (by omega)

/-- For every admissible `k`, the Kasami normalized derivative image has
exactly half the field. Odd `k` is the MCM theorem; even `k` is transported to
the odd complementary parameter `n-k`. -/
theorem kasami_half_size
    {n k : ℕ} (hkpos : 1 ≤ k) (hklt : k < n)
    (hkn : Nat.Coprime k n) (hcard : Fintype.card K = 2 ^ n) :
    2 * (derivativeImage k K).card = Fintype.card K := by
  rcases Nat.even_or_odd k with hke | hko
  · have hcomp_odd := odd_complement_of_even_coprime hklt hkn hke
    have hk_le : k ≤ n := hklt.le
    have hcomp_lt : n - k < n := by omega
    have hcomp_coprime : Nat.Coprime (n - k) n :=
      (Nat.coprime_self_sub_left hk_le).mpr hkn
    have hhalf_comp :
        2 * (derivativeImage (n - k) K).card = Fintype.card K :=
      kasami_half_size_odd hcomp_lt hcard hcomp_odd hcomp_coprime
    have hc := card_derivativeImage_complement (K := K) hk_le hcard
    rw [hc]
    exact hhalf_comp
  · exact kasami_half_size_odd hklt hcard hko hkn

end

end KasamiCyclicAdditive
