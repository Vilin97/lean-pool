/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import LeanPool.KasamiCyclicAdditive.Geometry.PointFrobenius
import LeanPool.KasamiCyclicAdditive.Geometry.Descent.Arithmetic
import LeanPool.KasamiCyclicAdditive.Geometry.IsogenyFactor

/-!
# The Frobenius annihilator on `E(K)`

For a finite field `K` with `|K| = 2^n`, the `n`-th power of the Frobenius
endomorphism is the identity on `E(K)`, simply because every coordinate
satisfies `x^(2^n) = x`.  In even dimension `n = 2j` the CM relation
`π² = [-2]` additionally gives `π^n = [(-2)^j]`, so comparing the two
descriptions shows that

  `nn n = (-2)^j - 1`

annihilates `E(K)`.  That is the hypothesis `hann` of
`Isogeny.gMap_bijective`, and together with `Descent.isCoprime_nn`
it makes `G` bijective on `E(K)` — no algebraic closure and no kernel
decomposition.
-/

open KasamiCyclicAdditive.FermatCubic

namespace KasamiCyclicAdditive.PointFrobenius

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-- The `n`-th Frobenius power is the identity on `K`-rational points. -/
theorem frobEnd_pow_card_eq {n : ℕ} (hcard : Fintype.card K = 2 ^ n)
    (P : (fer K).toAffine.Point) : (frobEnd K ^ n) P = P := by
  have hpow : ∀ x : K, x ^ 2 ^ n = x := by
    intro x; rw [← hcard]; exact FiniteField.pow_card x
  rcases point_repr P with rfl | ⟨a, ha, rfl⟩ | ⟨w, t, h, rfl⟩
  · simp
  · rw [frobEnd_pow_ptInf]
    congr 1
    exact hpow a
  · rw [frobEnd_pow_pt]; exact pt_congr _ _ (hpow w) (hpow t)

omit [Fintype K] in
/-- The abstract iterate `Isogeny.piIter` agrees with the Frobenius
endomorphism power. -/
theorem piIter_frobPt (k : ℕ) (P : (fer K).toAffine.Point) :
    Isogeny.piIter (frobPt K) k P = (frobEnd K ^ k) P := by
  induction k generalizing P with
  | zero => rfl
  | succ k ih =>
      rw [Isogeny.piIter, ih]
      change frobPt K ((frobEnd K ^ k) P) = _
      rw [pow_succ']
      rfl

/-- `nn n` annihilates `E(K)` in even dimension. -/
theorem nn_smul_eq_zero {n : ℕ} (hn : Even n) (hcard : Fintype.card K = 2 ^ n)
    (P : (fer K).toAffine.Point) : Descent.nn n • P = 0 := by
  obtain ⟨j, hj⟩ := hn
  have hn2 : n = 2 * j := by omega
  have h1 : (frobEnd K ^ n) P = P := frobEnd_pow_card_eq hcard P
  have h2 : (frobEnd K ^ n) P = ((-2 : ℤ) ^ j) • P := by
    rw [hn2, ← piIter_frobPt]
    exact Isogeny.piIter_even (frobPt K) (fun x => frobPt_frobPt (K := K) x) j P
  have hcn : Descent.cN n = (-2 : ℤ) ^ j := by
    unfold Descent.cN; congr 1; omega
  have : ((-2 : ℤ) ^ j) • P = P := by rw [← h2, h1]
  unfold Descent.nn
  rw [hcn, sub_smul, this, one_smul, sub_self]

/-! ### Inverting `G` on `E(K)` -/

/-- For odd `k = 2r+1` in even dimension, the prime-to-3 factor `G` is a
bijection of `E(K)`, so every point has a `G`-preimage.

The 3-primary obstruction is the separate factor `1 + π`, and `G` is inverted by
Bézout against the annihilator `nn n`, over `K` itself.  The factorization
`(1 + π) ∘ G = 1 + π^k` is `Isogeny.gMap_factor`, applied by the caller where it
is needed. -/
theorem exists_gMap_preimage {n k m : ℕ} (hn : Even n) (hk : Odd k)
    (hcard : Fintype.card K = 2 ^ n) (he : 2 ^ k + 1 = 3 * m)
    (hm : Nat.Coprime m (2 ^ n - 1)) (R : (fer K).toAffine.Point) :
    ∃ (a b : ℤ) (r : ℕ) (Y : (fer K).toAffine.Point),
      k = 2 * r + 1 ∧ a + 2 * b = 1 ∧ a - b = (-2 : ℤ) ^ r ∧
      Isogeny.gMap (frobPt K) a b Y = R := by
  obtain ⟨r, hr⟩ := hk
  have he' : 2 ^ (2 * r + 1) + 1 = 3 * m := by rw [← hr]; exact he
  obtain ⟨a, b, hab1, hab2, hnorm⟩ := Isogeny.exists_factor_coefficients he'
  have hbij := Isogeny.gMap_bijective (frobPt K) (m := m) (N := Descent.nn n)
    (fun x => frobPt_frobPt (K := K) x) hnorm
    (fun x => nn_smul_eq_zero hn hcard x)
    ((Descent.isCoprime_nn hn hm).symm)
  obtain ⟨Y, hY⟩ := hbij.2 R
  exact ⟨a, b, r, Y, hr, hab1, hab2, hY⟩


end KasamiCyclicAdditive.PointFrobenius
