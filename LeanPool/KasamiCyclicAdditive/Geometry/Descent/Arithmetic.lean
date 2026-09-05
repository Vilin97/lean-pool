/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude

/-!
# Arithmetic facts for the descent

This file formalises the arithmetic behind the even-dimensional descent step.
For even `n`, `c_n = (-2)^(n/2)` is the integer with `π^n = [c_n]`, and
`N = c_n - 1`:

* `cN_sq` : `c_n^2 = Q = 2^n`;
* `nn_dvd` : `N ∣ Q - 1`, since `Q - 1 = (c_n - 1)(c_n + 1)`;
* `isCoprime_nn` : `gcd(N, m) = 1` whenever `gcd(m, Q - 1) = 1`.

`N` is the annihilator of `E(K)` used by `Isogeny.gMap_bijective`; see
`Geometry/FrobeniusAnnihilator.lean`.
-/

namespace KasamiCyclicAdditive.Descent


section EvenN

variable (n : ℕ)

/-- `c_n = (-2)^(n/2)`, the integer with `π^n = [c_n]` for even `n`. -/
def cN : ℤ := (-2) ^ (n / 2)

/-- `N = c_n - 1`. -/
def nn : ℤ := cN n - 1

variable {n}

/-- `c_n^2 = Q = 2^n` for even `n`. -/
theorem cN_sq (hn : Even n) : (cN n) ^ 2 = 2 ^ n := by
  obtain ⟨j, rfl⟩ := hn
  have hj : (j + j) / 2 = j := by omega
  unfold cN
  rw [hj, ← pow_mul, show j * 2 = 2 * j by ring, pow_mul,
    show j + j = 2 * j by ring, pow_mul]
  norm_num

/-- `N ∣ Q - 1`, since `Q - 1 = (c_n-1)(c_n+1)`. -/
theorem nn_dvd (hn : Even n) : nn n ∣ (2 ^ n - 1 : ℤ) := by
  refine ⟨cN n + 1, ?_⟩
  have h := cN_sq hn
  unfold nn
  nlinarith [h]


/-- `gcd(N,m) = 1` follows from `gcd(m,Q-1)=1` and `N ∣ Q-1`. -/
theorem isCoprime_nn {m : ℕ} (hn : Even n) (hm : Nat.Coprime m (2 ^ n - 1)) :
    IsCoprime (nn n) (m : ℤ) := by
  have hle : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
  have hcast : (((2 ^ n - 1 : ℕ) : ℤ)) = (2 ^ n - 1 : ℤ) := by
    push_cast [Nat.cast_sub hle]
    ring
  have h : IsCoprime ((m : ℤ)) ((2 ^ n - 1 : ℤ)) := by
    rw [← hcast]
    exact_mod_cast Nat.isCoprime_iff_coprime.mpr hm
  exact (h.symm).of_isCoprime_of_dvd_left (nn_dvd hn)


end EvenN

end KasamiCyclicAdditive.Descent
