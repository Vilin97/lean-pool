/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.LowerBound.Counting.Points
import LeanPool.Nikodym.Nikodym.LowerBound.InterpolationCut
import LeanPool.Nikodym.Nikodym.LowerBound.Arithmetic.Multiplicity
import LeanPool.Nikodym.Nikodym.LowerBound.Counting.Components
import LeanPool.Nikodym.Nikodym.LowerBound.Counting.Curves

/-!
# The integer-power carrier theorem

This file implements blueprint node **C09** of the lower-bound side of the sharp finite-field
Nikodym exponent.

Let `F ⊆ K`, `q = |F|`, `d ≥ 2`, `C = 8 d² + 1`, and let `I` be a prime ideal of
`P_d = MvPolynomial (Fin d) K` of quotient dimension `k ≥ 1` and degree `Δ`. If a private family of
`L` lines lies on `I` (every line ideal contains `I`), then with `m_k = 2 ^ (k - 1)`,

`L ^ m_k * q ≤ (C Δ) ^ m_k * q ^ (k m_k)`.

This is `PrivateFamily.carrier_bound`, proved by induction on `k` over all private families at
once (the index type of the family changes in the inductive step). The base case `k = 1` is the
curve case C08. In the step `k + 1 ≥ 2`, put `M = Δ q ^ (k + 1)`, so `L ≤ M` by the point count
C01, and `r = 8 d² M / L + 1` (C05). If `q L < C M`, the bound follows by raising `q L ≤ C M` to
the power `2 m_k`; otherwise `8 d² ≤ r ≤ q` and `8 d² M < r L`, the interpolation cut C04 yields
`g`, the assignment C06 and selection C07 yield a component `J` of quotient dimension `k` with a
private subfamily of `#s` lines and `L deg J ≤ #s (T deg I)`, and the inductive hypothesis on `J`
gives the bound after the exact integer computation of Section 5 of the blueprint
(`carrier_step_arith`).

All arithmetic is in `ℕ`; no real roots enter.
-/

namespace Nikodym.LowerBound

open Finset

universe u

variable {K : Type*} [Field K] {d : ℕ} {F : Type*} [Field F] [Fintype F] [Algebra F K]

/-! ### Exact arithmetic of the induction -/

/-- Blueprint C09 (small case): if `q L ≤ X` and `0 < m`, then `L ^ m * q ≤ X ^ m`, since
`q ≤ q ^ m`. -/
theorem pow_mul_le_of_mul_le {L X q m : ℕ} (hm : 0 < m) (h : q * L ≤ X) :
    L ^ m * q ≤ X ^ m :=
  calc L ^ m * q ≤ L ^ m * q ^ m := Nat.mul_le_mul_left _ (Nat.le_self_pow hm.ne' q)
    _ = (q * L) ^ m := by ring
    _ ≤ X ^ m := Nat.pow_le_pow_left h m

/-- Blueprint C09 (inductive step), Section 5 of the blueprint. From the inductive hypothesis
`Ls ^ n * q ≤ (C ΔJ) ^ n * q ^ (k n)` on the selected component, the selection inequality
`L ΔJ ≤ Ls (T Δ)`, the degree bound `T ≤ r q` and the multiplicity bound
`r L ≤ C Δ q ^ (k + 1)`, deduce `L ^ (2 n) * q ≤ (C Δ) ^ (2 n) * q ^ ((k + 1) 2 n)`. -/
theorem carrier_step_arith {L Ls ΔJ Δ T r q C k n : ℕ} (hΔJ : 0 < ΔJ)
    (h1 : Ls ^ n * q ≤ (C * ΔJ) ^ n * q ^ (k * n))
    (h2 : L * ΔJ ≤ Ls * (T * Δ))
    (h3 : T ≤ r * q)
    (h4 : r * L ≤ C * (Δ * q ^ (k + 1))) :
    L ^ (n * 2) * q ≤ (C * Δ) ^ (n * 2) * q ^ ((k + 1) * (n * 2)) := by
  -- multiply the selection inequality by the inductive hypothesis, then cancel `ΔJ ^ n`
  have key1 : ΔJ ^ n * (L ^ n * q) ≤ ΔJ ^ n * ((C * Δ) ^ n * T ^ n * q ^ (k * n)) :=
    calc ΔJ ^ n * (L ^ n * q) = (L * ΔJ) ^ n * q := by ring
      _ ≤ (Ls * (T * Δ)) ^ n * q := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h2 n)
      _ = (T * Δ) ^ n * (Ls ^ n * q) := by ring
      _ ≤ (T * Δ) ^ n * ((C * ΔJ) ^ n * q ^ (k * n)) := Nat.mul_le_mul_left _ h1
      _ = ΔJ ^ n * ((C * Δ) ^ n * T ^ n * q ^ (k * n)) := by ring
  have key2 : L ^ n * q ≤ (C * Δ) ^ n * T ^ n * q ^ (k * n) :=
    Nat.le_of_mul_le_mul_left key1 (pow_pos hΔJ n)
  -- replace `T` by `r q`
  have key3 : L ^ n * q ≤ (C * Δ) ^ n * r ^ n * q ^ ((k + 1) * n) :=
    calc L ^ n * q ≤ (C * Δ) ^ n * T ^ n * q ^ (k * n) := key2
      _ ≤ (C * Δ) ^ n * (r * q) ^ n * q ^ (k * n) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h3 n))
      _ = (C * Δ) ^ n * r ^ n * q ^ ((k + 1) * n) := by ring
  -- multiply by `L ^ n` and use `r L ≤ C Δ q ^ (k + 1)`
  calc L ^ (n * 2) * q = L ^ n * (L ^ n * q) := by ring
    _ ≤ L ^ n * ((C * Δ) ^ n * r ^ n * q ^ ((k + 1) * n)) := Nat.mul_le_mul_left _ key3
    _ = (C * Δ) ^ n * (r * L) ^ n * q ^ ((k + 1) * n) := by ring
    _ ≤ (C * Δ) ^ n * (C * (Δ * q ^ (k + 1))) ^ n * q ^ ((k + 1) * n) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h4 n))
    _ = (C * Δ) ^ (n * 2) * q ^ ((k + 1) * (n * 2)) := by ring

/-! ### The carrier theorem -/

/-- Blueprint C09: the integer-power carrier theorem. For `d ≥ 2`, `C = 8 d² + 1`, `k ≥ 1`, a
prime `I` of quotient dimension `k` and degree `Δ`, and a private family of `L` lines lying on `I`,
`L ^ (2 ^ (k - 1)) * q ≤ (C Δ) ^ (2 ^ (k - 1)) * q ^ (k 2 ^ (k - 1))`. The statement is
universally quantified over the index type of the family, since the inductive step passes to a
subfamily. -/
theorem PrivateFamily.carrier_bound (H : AlgebraInterface K d) (hd : 2 ≤ d)
    {k : ℕ} (hk : 1 ≤ k) :
    ∀ {E : Type u} [Fintype E] (P : PrivateFamily F d E) {I : Ideal (MvPolynomial (Fin d) K)},
      I.IsPrime → quotDim I = k → (∀ e, I ≤ P.lineIdeal (K := K) e) →
      Fintype.card E ^ 2 ^ (k - 1) * Fintype.card F ≤
        ((8 * d ^ 2 + 1) * degree I) ^ 2 ^ (k - 1) * Fintype.card F ^ (k * 2 ^ (k - 1)) := by
  induction k, hk using Nat.le_induction with
  | base =>
    -- the curve case C08: `L ≤ Δ ≤ C Δ`
    intro E _ P I hI hdim hIP
    have := hI
    simp only [Nat.sub_self, pow_zero, pow_one, one_mul]
    refine Nat.mul_le_mul_right _ ((P.card_le_degree_of_quotDim_le_one hdim.le hIP).trans ?_)
    exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  | succ k hk ih =>
    intro E _ P I hI hdim hIP
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at ih ⊢
    rw [show (2 : ℕ) ^ (j + 1) = 2 ^ j * 2 from pow_succ 2 j]
    set q := Fintype.card F
    set L := Fintype.card E
    set Δ := degree I
    set n := 2 ^ j
    have hn : 0 < n := by positivity
    -- the trivial case `L = 0`
    rcases Nat.eq_zero_or_pos L with hL0 | hL
    · rw [hL0, zero_pow (by omega), zero_mul]
      exact Nat.zero_le _
    -- point counting C01: `L ≤ M = Δ q ^ (k + 1)`
    have hLM : L ≤ Δ * q ^ (j + 1 + 1) := by
      have h := P.card_le_degree_mul_pow H hI hIP
      rwa [hdim] at h
    have hM : 0 < Δ * q ^ (j + 1 + 1) := hL.trans_le hLM
    rcases lt_or_ge (q * L) ((8 * d ^ 2 + 1) * (Δ * q ^ (j + 1 + 1))) with hsmall | hbig
    · -- small case: raise `q L ≤ C M` to the power `2 n`
      calc L ^ (n * 2) * q ≤ ((8 * d ^ 2 + 1) * (Δ * q ^ (j + 1 + 1))) ^ (n * 2) :=
            pow_mul_le_of_mul_le (by omega) hsmall.le
        _ = ((8 * d ^ 2 + 1) * Δ) ^ (n * 2) * q ^ ((j + 1 + 1) * (n * 2)) := by
            simp only [mul_pow, ← pow_mul]
            ring
    · -- multiplicity choice C05
      have har : 8 * d ^ 2 ≤ 8 * d ^ 2 * (Δ * q ^ (j + 1 + 1)) / L + 1 :=
        le_r _ _ _ hL hLM
      have hrq : 8 * d ^ 2 * (Δ * q ^ (j + 1 + 1)) / L + 1 ≤ q :=
        r_le_of_le _ _ _ _ hL hM hbig
      have hlt : 8 * d ^ 2 * (Δ * q ^ (j + 1 + 1)) <
          (8 * d ^ 2 * (Δ * q ^ (j + 1 + 1)) / L + 1) * L :=
        lt_mul _ _ _ hL
      have hrL : (8 * d ^ 2 * (Δ * q ^ (j + 1 + 1)) / L + 1) * L ≤
          (8 * d ^ 2 + 1) * (Δ * q ^ (j + 1 + 1)) :=
        (mul_le _ _ _).trans (le_mul_add _ _ _ hLM)
      -- interpolation cut C04
      obtain ⟨g, hgI, hgT, hg, -⟩ :=
        P.exists_cut_of_card_pos H hI hd (by omega) hIP hL har hrq (by rw [hdim]; exact hlt)
      -- component assignment and selection C06 + C07
      have : Nonempty E := Fintype.card_pos_iff.mp hL
      obtain ⟨J, s, hJ, hJdim, hJdeg, -, hJle, hcard⟩ :=
        P.exists_component_family H hI (by omega) hIP hgI hgT hg
      have hJk : quotDim J = j + 1 := by omega
      -- inductive hypothesis on the subfamily carried by `J`
      have ih' := ih (P.restrict s) hJ hJk hJle
      rw [Fintype.card_coe] at ih'
      have hT : (8 * d ^ 2 * (Δ * q ^ (j + 1 + 1)) / L + 1) * (q - 1) - 1 ≤
          (8 * d ^ 2 * (Δ * q ^ (j + 1 + 1)) / L + 1) * q :=
        (Nat.sub_le _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
      exact carrier_step_arith hJdeg ih' hcard hT hrL

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
