/-
Copyright (c) 2026 Ho Boon Suan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ho Boon Suan
-/

/-
# Pippenger expander construction (Lemma 4.1)

This file isolates the Pippenger probabilistic construction from Section 4 of
the companion paper. It provides:

1. A `PippengerRowCertificate` structure capturing the hypotheses of Lemma 4.1.
2. Four row-specific numerical certificates (E₁–E₄).
3. Row-specific probabilistic/counting constructions for E₁–E₄.
4. The combined `pippenger_required_expanders` theorem.

**Reference**: Section 4 and the table in Section 5 of
the companion paper.
-/
import LeanPool.KaltonRoberts.Defs
import LeanPool.KaltonRoberts.Numerical
import LeanPool.KaltonRoberts.PhiAnalysis
import LeanPool.KaltonRoberts.PippengerProof

/-!
# Pippenger expander construction

Row certificates and row-specific constructions for the probabilistic expander
argument used in the Kalton-Roberts bound.
-/

namespace KaltonRoberts

open Finset BigOperators

/-! ## Row certificate structure -/

/-- A `PippengerRowCertificate` captures exactly the hypotheses of Lemma 4.1
for one row of the expander table. Given parameters `α r θ c δ`, it asserts:
- Range conditions: `0 < α < θ < 1`, `3 ≤ r`, `r < c`, `θ = r/c`
- Tail bound: `e² · θ^{1−r} · δ^{r−2} < 1/20`
- Entropy negativity: `Φ_{r,θ}(x) < 0` for all `x ∈ [δ, α]`

The paper uses `c = r/θ`. For the four rows:
- E₁: r = 4, θ = 1/3, c = 12
- E₂: r = 4, θ = 4/7, c = 7
- E₃: r = 4, θ = 2/7, c = 14
- E₄: r = 5, θ = 5/11, c = 11
-/
structure PippengerRowCertificate (α : ℚ) (r : ℕ) (θ : ℚ) (c : ℕ) (δ : ℚ) : Prop where
  /-- `0 < α` -/
  α_pos : (0 : ℚ) < α
  /-- `α < θ` -/
  α_lt_θ : α < θ
  /-- `θ < 1` -/
  θ_lt_one : θ < 1
  /-- `3 ≤ r` -/
  r_ge_three : 3 ≤ r
  /-- `r < c` -/
  r_lt_c : r < c
  /-- `θ = r / c` (in ℚ) -/
  θ_eq : θ = (r : ℚ) / (c : ℚ)
  /-- `0 < δ` -/
  δ_pos : (0 : ℚ) < δ
  /-- `δ < α` -/
  δ_lt_α : δ < α
  /-- Tail bound (real): `e² · (θ : ℝ)^{1−r} · (δ : ℝ)^{r−2} < 1/20` -/
  tail_bound : Real.exp 2 * (θ : ℝ) ^ (1 - (r : ℤ)) * (δ : ℝ) ^ ((r : ℤ) - 2) < 1 / 20
  /-- Entropy negativity: `Φ_{r,θ}(x) < 0` for all `x ∈ [δ, α]` -/
  phi_neg : ∀ x : ℝ, (δ : ℝ) ≤ x → x ≤ (α : ℝ) → Phi (r : ℝ) (θ : ℝ) x < 0

/-! ## Tail bound proofs -/

/-- Tail bound for E₁: `e² · (1/3)^{-3} · (1/100)^2 < 1/20` -/
theorem tail_bound_real_E₁ :
    Real.exp 2 * ((1 / 3 : ℚ) : ℝ) ^ (1 - (4 : ℤ)) * ((1 / 100 : ℚ) : ℝ) ^ ((4 : ℤ) - 2) < 1 / 20 :=
      by
  have he := e_sq_lt
  have h1 : ((1 / 3 : ℚ) : ℝ) ^ (1 - (4 : ℤ)) = 27 := by
    push_cast; norm_num [zpow_neg, zpow_natCast]
  have h2 : ((1 / 100 : ℚ) : ℝ) ^ ((4 : ℤ) - 2) = 1 / 10000 := by
    push_cast; norm_num [zpow_natCast]
  rw [h1, h2]; nlinarith

/-- Tail bound for E₂: `e² · (4/7)^{-3} · (1/100)^2 < 1/20` -/
theorem tail_bound_real_E₂ :
    Real.exp 2 * ((4 / 7 : ℚ) : ℝ) ^ (1 - (4 : ℤ)) * ((1 / 100 : ℚ) : ℝ) ^ ((4 : ℤ) - 2) < 1 / 20 :=
      by
  have he := e_sq_lt
  have h1 : ((4 / 7 : ℚ) : ℝ) ^ (1 - (4 : ℤ)) = (7 / 4 : ℝ) ^ (3 : ℕ) := by
    push_cast; norm_num [zpow_neg, zpow_natCast, inv_eq_one_div]
  have h2 : ((1 / 100 : ℚ) : ℝ) ^ ((4 : ℤ) - 2) = 1 / 10000 := by
    push_cast; norm_num [zpow_natCast]
  rw [h1, h2]
  have h3 : (7 / 4 : ℝ) ^ (3 : ℕ) = 343 / 64 := by norm_num
  rw [h3]; nlinarith

/-- Tail bound for E₃: `e² · (2/7)^{-3} · (1/100)^2 < 1/20` -/
theorem tail_bound_real_E₃ :
    Real.exp 2 * ((2 / 7 : ℚ) : ℝ) ^ (1 - (4 : ℤ)) * ((1 / 100 : ℚ) : ℝ) ^ ((4 : ℤ) - 2) < 1 / 20 :=
      by
  have he := e_sq_lt
  have h1 : ((2 / 7 : ℚ) : ℝ) ^ (1 - (4 : ℤ)) = (7 / 2 : ℝ) ^ (3 : ℕ) := by
    push_cast; norm_num [zpow_neg, zpow_natCast, inv_eq_one_div]
  have h2 : ((1 / 100 : ℚ) : ℝ) ^ ((4 : ℤ) - 2) = 1 / 10000 := by
    push_cast; norm_num [zpow_natCast]
  rw [h1, h2]
  have h3 : (7 / 2 : ℝ) ^ (3 : ℕ) = 343 / 8 := by norm_num
  rw [h3]; nlinarith

/-- Tail bound for E₄: `e² · (5/11)^{-4} · (1/100)^3 < 1/20` -/
theorem tail_bound_real_E₄ :
    Real.exp 2 * ((5 / 11 : ℚ) : ℝ) ^ (1 - (5 : ℤ)) * ((1 / 100 : ℚ) : ℝ) ^ ((5 : ℤ) - 2) < 1 / 20
      := by
  have he := e_sq_lt
  have h1 : ((5 / 11 : ℚ) : ℝ) ^ (1 - (5 : ℤ)) = (11 / 5 : ℝ) ^ (4 : ℕ) := by
    push_cast; norm_num [zpow_neg, zpow_natCast, inv_eq_one_div]
  have h2 : ((1 / 100 : ℚ) : ℝ) ^ ((5 : ℤ) - 2) = 1 / 1000000 := by
    push_cast; norm_num [zpow_natCast]
  rw [h1, h2]
  have h3 : (11 / 5 : ℝ) ^ (4 : ℕ) = 14641 / 625 := by norm_num
  rw [h3]; nlinarith

/-! ## Phi negativity on intervals

For each Pippenger row, the proof combines:
1. endpoint log certificates from `LogBounds.lean`,
2. derivative and convexity facts from `PhiDeriv.lean`, and
3. the endpoint-maximum property for convex functions.

**Reference**: Section 4 of the companion paper.
-/

/-- Phi negativity on `[1/100, α₁]` for E₁ `(r=4, θ=1/3)`. -/
theorem Phi_neg_E₁ : ∀ x : ℝ, ((1/100 : ℚ) : ℝ) ≤ x → x ≤ ((1003/10000 : ℚ) : ℝ) →
    Phi ((4 : ℕ) : ℝ) ((1/3 : ℚ) : ℝ) x < 0 := by
  intro x hδ hx
  push_cast at hδ hx ⊢
  exact convexOn_Icc_neg_of_endpoints (by norm_num)
    convexOn_Phi_E₁ (by linarith [Phi_E₁_at_delta]) (by linarith [Phi_E₁_at_alpha])
    x hδ hx

/-- Phi negativity on `[1/100, 3009/10000]` for E₂ `(r=4, θ=4/7)`. -/
theorem Phi_neg_E₂ : ∀ x : ℝ, ((1/100 : ℚ) : ℝ) ≤ x → x ≤ ((3009/10000 : ℚ) : ℝ) →
    Phi ((4 : ℕ) : ℝ) ((4/7 : ℚ) : ℝ) x < 0 := by
  intro x hδ hx
  push_cast at hδ hx ⊢
  exact convexOn_Icc_neg_of_endpoints (by norm_num)
    convexOn_Phi_E₂ (by linarith [Phi_E₂_at_delta]) (by linarith [Phi_E₂_at_alpha])
    x hδ hx

/-- Phi negativity on `[1/100, 47/625]` for E₃ `(r=4, θ=2/7)`. -/
theorem Phi_neg_E₃ : ∀ x : ℝ, ((1/100 : ℚ) : ℝ) ≤ x → x ≤ ((47/625 : ℚ) : ℝ) →
    Phi ((4 : ℕ) : ℝ) ((2/7 : ℚ) : ℝ) x < 0 := by
  intro x hδ hx
  push_cast at hδ hx ⊢
  exact convexOn_Icc_neg_of_endpoints (by norm_num)
    convexOn_Phi_E₃ (by linarith [Phi_E₃_at_delta]) (by linarith [Phi_E₃_at_alpha])
    x hδ hx

/-- Phi negativity on `[1/100, 329/1250]` for E₄ `(r=5, θ=5/11)`. -/
theorem Phi_neg_E₄ : ∀ x : ℝ, ((1/100 : ℚ) : ℝ) ≤ x → x ≤ ((329/1250 : ℚ) : ℝ) →
    Phi ((5 : ℕ) : ℝ) ((5/11 : ℚ) : ℝ) x < 0 := by
  intro x hδ hx
  push_cast at hδ hx ⊢
  exact convexOn_Icc_neg_of_endpoints (by norm_num)
    convexOn_Phi_E₄ (by linarith [Phi_E₄_at_delta]) (by linarith [Phi_E₄_at_alpha])
    x hδ hx

theorem Phi_margin_E₁ : ∀ x : ℝ, 1 / 100 ≤ x → x ≤ 1003 / 10000 →
    Phi 4 (1 / 3) x ≤ -(1 : ℝ) / 1000 := by
  intro x hδ hx
  have hle := convexOn_Phi_E₁.le_max_of_mem_Icc
    (Set.left_mem_Icc.mpr (by norm_num : (1 / 100 : ℝ) ≤ 1003 / 10000))
    (Set.right_mem_Icc.mpr (by norm_num : (1 / 100 : ℝ) ≤ 1003 / 10000))
    ⟨hδ, hx⟩
  have hmax : max (Phi 4 (1 / 3) (1 / 100))
      (Phi 4 (1 / 3) (1003 / 10000)) < -(1 : ℝ) / 1000 :=
    max_lt Phi_E₁_at_delta Phi_E₁_at_alpha
  exact le_of_lt (lt_of_le_of_lt hle hmax)

theorem Phi_margin_E₂ : ∀ x : ℝ, 1 / 100 ≤ x → x ≤ 3009 / 10000 →
    Phi 4 (4 / 7) x ≤ -(1 : ℝ) / 1000 := by
  intro x hδ hx
  have hle := convexOn_Phi_E₂.le_max_of_mem_Icc
    (Set.left_mem_Icc.mpr (by norm_num : (1 / 100 : ℝ) ≤ 3009 / 10000))
    (Set.right_mem_Icc.mpr (by norm_num : (1 / 100 : ℝ) ≤ 3009 / 10000))
    ⟨hδ, hx⟩
  have hmax : max (Phi 4 (4 / 7) (1 / 100))
      (Phi 4 (4 / 7) (3009 / 10000)) < -(1 : ℝ) / 1000 :=
    max_lt Phi_E₂_at_delta Phi_E₂_at_alpha
  exact le_of_lt (lt_of_le_of_lt hle hmax)

theorem Phi_margin_E₃ : ∀ x : ℝ, 1 / 100 ≤ x → x ≤ 47 / 625 →
    Phi 4 (2 / 7) x ≤ -(1 : ℝ) / 1000 := by
  intro x hδ hx
  have hle := convexOn_Phi_E₃.le_max_of_mem_Icc
    (Set.left_mem_Icc.mpr (by norm_num : (1 / 100 : ℝ) ≤ 47 / 625))
    (Set.right_mem_Icc.mpr (by norm_num : (1 / 100 : ℝ) ≤ 47 / 625))
    ⟨hδ, hx⟩
  have hmax : max (Phi 4 (2 / 7) (1 / 100))
      (Phi 4 (2 / 7) (47 / 625)) < -(1 : ℝ) / 1000 :=
    max_lt Phi_E₃_at_delta Phi_E₃_at_alpha
  exact le_of_lt (lt_of_le_of_lt hle hmax)

theorem Phi_margin_E₄ : ∀ x : ℝ, 1 / 100 ≤ x → x ≤ 329 / 1250 →
    Phi 5 (5 / 11) x ≤ -(1 : ℝ) / 1000 := by
  intro x hδ hx
  have hle := convexOn_Phi_E₄.le_max_of_mem_Icc
    (Set.left_mem_Icc.mpr (by norm_num : (1 / 100 : ℝ) ≤ 329 / 1250))
    (Set.right_mem_Icc.mpr (by norm_num : (1 / 100 : ℝ) ≤ 329 / 1250))
    ⟨hδ, hx⟩
  have hmax : max (Phi 5 (5 / 11) (1 / 100))
      (Phi 5 (5 / 11) (329 / 1250)) < -(1 : ℝ) / 1000 :=
    max_lt Phi_E₄_at_delta Phi_E₄_at_alpha
  exact le_of_lt (lt_of_le_of_lt hle hmax)

/-! ## Row certificates -/

/-- Row certificate for E₁: `α = 1003/10000, r = 4, θ = 1/3, c = 12, δ = 1/100`. -/
theorem row_certificate_E₁ : PippengerRowCertificate (1003/10000) 4 (1/3) 12 (1/100) where
  α_pos := by norm_num
  α_lt_θ := by norm_num
  θ_lt_one := by norm_num
  r_ge_three := by norm_num
  r_lt_c := by norm_num
  θ_eq := by norm_num
  δ_pos := by norm_num
  δ_lt_α := by norm_num
  tail_bound := tail_bound_real_E₁
  phi_neg := Phi_neg_E₁

/-- Row certificate for E₂: `α = 3009/10000, r = 4, θ = 4/7, c = 7, δ = 1/100`. -/
theorem row_certificate_E₂ : PippengerRowCertificate (3009/10000) 4 (4/7) 7 (1/100) where
  α_pos := by norm_num
  α_lt_θ := by norm_num
  θ_lt_one := by norm_num
  r_ge_three := by norm_num
  r_lt_c := by norm_num
  θ_eq := by norm_num
  δ_pos := by norm_num
  δ_lt_α := by norm_num
  tail_bound := tail_bound_real_E₂
  phi_neg := Phi_neg_E₂

/-- Row certificate for E₃: `α = 47/625, r = 4, θ = 2/7, c = 14, δ = 1/100`. -/
theorem row_certificate_E₃ : PippengerRowCertificate (47/625) 4 (2/7) 14 (1/100) where
  α_pos := by norm_num
  α_lt_θ := by norm_num
  θ_lt_one := by norm_num
  r_ge_three := by norm_num
  r_lt_c := by norm_num
  θ_eq := by norm_num
  δ_pos := by norm_num
  δ_lt_α := by norm_num
  tail_bound := tail_bound_real_E₃
  phi_neg := Phi_neg_E₃

/-- Row certificate for E₄: `α = 329/1250, r = 5, θ = 5/11, c = 11, δ = 1/100`. -/
theorem row_certificate_E₄ : PippengerRowCertificate (329/1250) 5 (5/11) 11 (1/100) where
  α_pos := by norm_num
  α_lt_θ := by norm_num
  θ_lt_one := by norm_num
  r_ge_three := by norm_num
  r_lt_c := by norm_num
  θ_eq := by norm_num
  δ_pos := by norm_num
  δ_lt_α := by norm_num
  tail_bound := tail_bound_real_E₄
  phi_neg := Phi_neg_E₄

/-! ## Row-specific bad-ratio estimates -/

theorem tail_bound_E₁_simplified :
    Real.exp 2 * 27 * ((1 / 100 : ℝ) ^ 2) < 1 / 20 := by
  have h := tail_bound_real_E₁
  norm_num at h ⊢
  exact h

theorem small_term_E₁
    (N L m : ℕ) (hN : 0 < N) (hm : 0 < m) (hmN : m ≤ N) (hmL : m ≤ L)
    (hNL : 4 * N = 12 * L) (hLreal : (L : ℝ) = (1 / 3 : ℝ) * (N : ℝ))
    (hsmall : (m : ℝ) / (N : ℝ) ≤ 1 / 100) :
    (N.choose m : ℝ) * (L.choose m : ℝ) *
        ((12 * m).choose (4 * m) : ℝ) / ((4 * N).choose (4 * m) : ℝ)
      ≤ ((1 / 20 : ℝ) ^ m) := by
  have hcmN : 12 * m ≤ 4 * N := by
    simp_all
  have hraw := pippenger_small_term_raw N L 4 12 m hm hmN hmL (by norm_num) hcmN
  refine le_trans hraw ?_
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hbase_eq :
      (Real.exp 1 * (N : ℝ) / (m : ℝ) *
          (Real.exp 1 * (L : ℝ) / (m : ℝ)) *
          (((12 * m : ℕ) : ℝ) / ((4 * N : ℕ) : ℝ)) ^ 4)
        =
      Real.exp 2 * 27 * (((m : ℝ) / (N : ℝ)) ^ 2) := by
    rw [hLreal]
    rw [show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
    norm_num [Nat.cast_mul]
    field_simp [hm_ne, hN_ne]
    ring
  have hx_nonneg : 0 ≤ (m : ℝ) / (N : ℝ) := by positivity
  have hx2_le : ((m : ℝ) / (N : ℝ)) ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ hx_nonneg hsmall 2
  have hbase_le : Real.exp 2 * 27 * (((m : ℝ) / (N : ℝ)) ^ 2) ≤ 1 / 20 := by
    have hcoef_nonneg : 0 ≤ Real.exp 2 * 27 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hx2_le hcoef_nonneg
    nlinarith [tail_bound_E₁_simplified, hmul]
  rw [hbase_eq]
  exact pow_le_pow_left₀ (by positivity) hbase_le m

theorem bad_ratio_sum_E₁_core (t : ℕ) (ht : 0 < t)
    (hdec : 50 * (((15000 * t : ℕ) : ℝ) ^ 2) *
        Real.exp (-(1 / 500 : ℝ) * ((15000 * t : ℕ) : ℝ)) < 1 / 2) :
    (∑ m ∈ Finset.Icc 1 (3009 * t),
      ((30000 * t).choose m : ℝ) * ((10000 * t).choose m : ℝ) *
        (((12 * m).choose (4 * m) : ℝ) / (((4 * (30000 * t)).choose (4 * m) : ℝ)))) < 1 := by
  let N := 30000 * t
  let L := 10000 * t
  let A := 3009 * t
  let D := 300 * t
  let B : ℝ := (((4 * N : ℕ) : ℝ) + 1) * Real.exp (-(N : ℝ) / 1000)
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hsum_le :
      (∑ m ∈ Finset.Icc 1 A,
        ((N.choose m : ℝ) * (L.choose m : ℝ) *
          (((12 * m).choose (4 * m) : ℝ) / (((4 * N).choose (4 * m) : ℝ)))))
        ≤ (1 / 20 : ℝ) / (1 - 1 / 20) + (N : ℝ) * B := by
    apply bad_sum_split A D N
      (fun m => ((N.choose m : ℝ) * (L.choose m : ℝ) *
          (((12 * m).choose (4 * m) : ℝ) / (((4 * N).choose (4 * m) : ℝ)))))
      (1 / 20) B
    · norm_num
    · norm_num
    · dsimp [B]; positivity
    · dsimp [A, N]
      simp_all
    · intro m hmI hmD
      have hmpos : 0 < m := (Finset.mem_Icc.mp hmI).1
      have hmA : m ≤ A := (Finset.mem_Icc.mp hmI).2
      have hmN : m ≤ N := by dsimp [A, N] at hmA ⊢; nlinarith
      have hmL : m ≤ L := by dsimp [A, L] at hmA ⊢; nlinarith
      have hsmall : (m : ℝ) / (N : ℝ) ≤ 1 / 100 := by
        rw [div_le_iff₀ (by exact_mod_cast hNpos)]
        have hmD' : (m : ℝ) ≤ (D : ℝ) := by exact_mod_cast hmD
        dsimp [D, N] at hmD' ⊢
        norm_num [Nat.cast_mul] at hmD' ⊢
        nlinarith
      have hs := small_term_E₁ N L m hNpos hmpos hmN hmL
        (by dsimp [N, L]; ring)
        (by dsimp [N, L]; norm_num [Nat.cast_mul]; ring)
        hsmall
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hs
    · intro m hmI hDm
      have hmpos : 0 < m := (Finset.mem_Icc.mp hmI).1
      have hmA : m ≤ A := (Finset.mem_Icc.mp hmI).2
      have hmN : m < N := by dsimp [A, N] at hmA ⊢; nlinarith [ht]
      have hmL : m < L := by dsimp [A, L] at hmA ⊢; nlinarith [ht]
      have hx_low : 1 / 100 ≤ (m : ℝ) / (N : ℝ) := by
        rw [le_div_iff₀ (by exact_mod_cast hNpos)]
        have hDm' : (D : ℝ) < (m : ℝ) := by exact_mod_cast hDm
        dsimp [D, N] at hDm' ⊢
        norm_num [Nat.cast_mul] at hDm' ⊢
        nlinarith
      have hx_high : (m : ℝ) / (N : ℝ) ≤ 1003 / 10000 := by
        rw [div_le_iff₀ (by exact_mod_cast hNpos)]
        have hmA' : (m : ℝ) ≤ (A : ℝ) := by exact_mod_cast hmA
        dsimp [A, N] at hmA' ⊢
        norm_num [Nat.cast_mul] at hmA' ⊢
        nlinarith
      have hphi := Phi_margin_E₁ ((m : ℝ) / (N : ℝ)) hx_low hx_high
      have hmterm := pippenger_mid_term_le N L 4 12 m (1 / 3 : ℝ)
        hNpos hmpos hmN hmL (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by dsimp [N, L]; norm_num [Nat.cast_mul]; ring)
        (by norm_num)
        hphi
      simpa [B, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmterm
  have hmid_small : (N : ℝ) * B < 1 / 2 := by
    have hpoly : (N : ℝ) * (((4 * N : ℕ) : ℝ) + 1) ≤
        50 * (((15000 * t : ℕ) : ℝ) ^ 2) := by
      dsimp [N]
      norm_num [Nat.cast_mul]
      have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
      nlinarith [sq_nonneg (t : ℝ), htR, ht1]
    have hexp_eq :
        Real.exp (-(N : ℝ) / 1000) =
          Real.exp (-(1 / 500 : ℝ) * ((15000 * t : ℕ) : ℝ)) := by
      dsimp [N]
      norm_num [Nat.cast_mul]
      ring_nf
    dsimp [B]
    rw [hexp_eq]
    calc
      (N : ℝ) * ((((4 * N : ℕ) : ℝ) + 1) *
          Real.exp (-(1 / 500 : ℝ) * ((15000 * t : ℕ) : ℝ)))
          = (N : ℝ) * (((4 * N : ℕ) : ℝ) + 1) *
          Real.exp (-(1 / 500 : ℝ) * ((15000 * t : ℕ) : ℝ)) := by ring
      _ ≤ 50 * (((15000 * t : ℕ) : ℝ) ^ 2) *
          Real.exp (-(1 / 500 : ℝ) * ((15000 * t : ℕ) : ℝ)) := by
            exact mul_le_mul_of_nonneg_right hpoly (by positivity)
      _ < 1 / 2 := hdec
  have hsum_final :
      (∑ m ∈ Finset.Icc 1 A,
        ((N.choose m : ℝ) * (L.choose m : ℝ) *
          (((12 * m).choose (4 * m) : ℝ) / (((4 * N).choose (4 * m) : ℝ)))))
        < 1 := by
    calc
      (∑ m ∈ Finset.Icc 1 A,
        ((N.choose m : ℝ) * (L.choose m : ℝ) *
          (((12 * m).choose (4 * m) : ℝ) / (((4 * N).choose (4 * m) : ℝ)))))
          ≤ (1 / 20 : ℝ) / (1 - 1 / 20) + (N : ℝ) * B := hsum_le
      _ < 1 := by norm_num; linarith
  simpa [N, L, A] using hsum_final

theorem tail_bound_E₂_simplified :
    Real.exp 2 * ((7 / 4 : ℝ) ^ 3) * ((1 / 100 : ℝ) ^ 2) < 1 / 20 := by
  have h := tail_bound_real_E₂
  norm_num at h ⊢
  exact h

theorem small_term_E₂
    (N L m : ℕ) (hN : 0 < N) (hm : 0 < m) (hmN : m ≤ N) (hmL : m ≤ L)
    (hNL : 4 * N = 7 * L) (hLreal : (L : ℝ) = (4 / 7 : ℝ) * (N : ℝ))
    (hsmall : (m : ℝ) / (N : ℝ) ≤ 1 / 100) :
    (N.choose m : ℝ) * (L.choose m : ℝ) *
        ((7 * m).choose (4 * m) : ℝ) / ((4 * N).choose (4 * m) : ℝ)
      ≤ ((1 / 20 : ℝ) ^ m) := by
  have hcmN : 7 * m ≤ 4 * N := by
    simp_all
  have hraw := pippenger_small_term_raw N L 4 7 m hm hmN hmL (by norm_num) hcmN
  refine le_trans hraw ?_
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hbase_eq :
      (Real.exp 1 * (N : ℝ) / (m : ℝ) *
          (Real.exp 1 * (L : ℝ) / (m : ℝ)) *
          (((7 * m : ℕ) : ℝ) / ((4 * N : ℕ) : ℝ)) ^ 4)
        =
      Real.exp 2 * ((7 / 4 : ℝ) ^ 3) * (((m : ℝ) / (N : ℝ)) ^ 2) := by
    rw [hLreal]
    rw [show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
    norm_num [Nat.cast_mul]
    field_simp [hm_ne, hN_ne]
    ring
  have hx_nonneg : 0 ≤ (m : ℝ) / (N : ℝ) := by positivity
  have hx2_le : ((m : ℝ) / (N : ℝ)) ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ hx_nonneg hsmall 2
  have hbase_le : Real.exp 2 * ((7 / 4 : ℝ) ^ 3) *
      (((m : ℝ) / (N : ℝ)) ^ 2) ≤ 1 / 20 := by
    have hcoef_nonneg : 0 ≤ Real.exp 2 * ((7 / 4 : ℝ) ^ 3) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hx2_le hcoef_nonneg
    nlinarith [tail_bound_E₂_simplified, hmul]
  rw [hbase_eq]
  exact pow_le_pow_left₀ (by positivity) hbase_le m

theorem bad_ratio_sum_E₂_core (t : ℕ) (ht : 0 < t)
    (hdec : 50 * (((35000 * t : ℕ) : ℝ) ^ 2) *
        Real.exp (-(1 / 500 : ℝ) * ((35000 * t : ℕ) : ℝ)) < 1 / 2) :
    (∑ m ∈ Finset.Icc 1 (21063 * t),
      ((70000 * t).choose m : ℝ) * ((40000 * t).choose m : ℝ) *
        (((7 * m).choose (4 * m) : ℝ) / (((4 * (70000 * t)).choose (4 * m) : ℝ)))) < 1 := by
  let N := 70000 * t
  let L := 40000 * t
  let A := 21063 * t
  let D := 700 * t
  let B : ℝ := (((4 * N : ℕ) : ℝ) + 1) * Real.exp (-(N : ℝ) / 1000)
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hsum_le :
      (∑ m ∈ Finset.Icc 1 A,
        ((N.choose m : ℝ) * (L.choose m : ℝ) *
          (((7 * m).choose (4 * m) : ℝ) / (((4 * N).choose (4 * m) : ℝ)))))
        ≤ (1 / 20 : ℝ) / (1 - 1 / 20) + (N : ℝ) * B := by
    apply bad_sum_split A D N
      (fun m => ((N.choose m : ℝ) * (L.choose m : ℝ) *
          (((7 * m).choose (4 * m) : ℝ) / (((4 * N).choose (4 * m) : ℝ)))))
      (1 / 20) B
    · norm_num
    · norm_num
    · dsimp [B]; positivity
    · dsimp [A, N]
      simp_all
    · intro m hmI hmD
      have hmpos : 0 < m := (Finset.mem_Icc.mp hmI).1
      have hmA : m ≤ A := (Finset.mem_Icc.mp hmI).2
      have hmN : m ≤ N := by dsimp [A, N] at hmA ⊢; nlinarith
      have hmL : m ≤ L := by dsimp [A, L] at hmA ⊢; nlinarith
      have hsmall : (m : ℝ) / (N : ℝ) ≤ 1 / 100 := by
        rw [div_le_iff₀ (by exact_mod_cast hNpos)]
        have hmD' : (m : ℝ) ≤ (D : ℝ) := by exact_mod_cast hmD
        dsimp [D, N] at hmD' ⊢
        norm_num [Nat.cast_mul] at hmD' ⊢
        nlinarith
      have hs := small_term_E₂ N L m hNpos hmpos hmN hmL
        (by dsimp [N, L]; ring)
        (by dsimp [N, L]; norm_num [Nat.cast_mul]; ring)
        hsmall
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hs
    · intro m hmI hDm
      have hmpos : 0 < m := (Finset.mem_Icc.mp hmI).1
      have hmA : m ≤ A := (Finset.mem_Icc.mp hmI).2
      have hmN : m < N := by dsimp [A, N] at hmA ⊢; nlinarith [ht]
      have hmL : m < L := by dsimp [A, L] at hmA ⊢; nlinarith [ht]
      have hx_low : 1 / 100 ≤ (m : ℝ) / (N : ℝ) := by
        rw [le_div_iff₀ (by exact_mod_cast hNpos)]
        have hDm' : (D : ℝ) < (m : ℝ) := by exact_mod_cast hDm
        dsimp [D, N] at hDm' ⊢
        norm_num [Nat.cast_mul] at hDm' ⊢
        nlinarith
      have hx_high : (m : ℝ) / (N : ℝ) ≤ 3009 / 10000 := by
        rw [div_le_iff₀ (by exact_mod_cast hNpos)]
        have hmA' : (m : ℝ) ≤ (A : ℝ) := by exact_mod_cast hmA
        dsimp [A, N] at hmA' ⊢
        norm_num [Nat.cast_mul] at hmA' ⊢
        nlinarith
      have hphi := Phi_margin_E₂ ((m : ℝ) / (N : ℝ)) hx_low hx_high
      have hmterm := pippenger_mid_term_le N L 4 7 m (4 / 7 : ℝ)
        hNpos hmpos hmN hmL (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by dsimp [N, L]; norm_num [Nat.cast_mul]; ring)
        (by norm_num)
        hphi
      simpa [B, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmterm
  have hmid_small : (N : ℝ) * B < 1 / 2 := by
    have hpoly : (N : ℝ) * (((4 * N : ℕ) : ℝ) + 1) ≤
        50 * (((35000 * t : ℕ) : ℝ) ^ 2) := by
      dsimp [N]
      norm_num [Nat.cast_mul]
      have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
      nlinarith [sq_nonneg (t : ℝ), htR, ht1]
    have hexp_eq :
        Real.exp (-(N : ℝ) / 1000) =
          Real.exp (-(1 / 500 : ℝ) * ((35000 * t : ℕ) : ℝ)) := by
      dsimp [N]
      norm_num [Nat.cast_mul]
      ring_nf
    dsimp [B]
    rw [hexp_eq]
    calc
      (N : ℝ) * ((((4 * N : ℕ) : ℝ) + 1) *
          Real.exp (-(1 / 500 : ℝ) * ((35000 * t : ℕ) : ℝ)))
          = (N : ℝ) * (((4 * N : ℕ) : ℝ) + 1) *
          Real.exp (-(1 / 500 : ℝ) * ((35000 * t : ℕ) : ℝ)) := by ring
      _ ≤ 50 * (((35000 * t : ℕ) : ℝ) ^ 2) *
          Real.exp (-(1 / 500 : ℝ) * ((35000 * t : ℕ) : ℝ)) := by
            exact mul_le_mul_of_nonneg_right hpoly (by positivity)
      _ < 1 / 2 := hdec
  have hsum_final :
      (∑ m ∈ Finset.Icc 1 A,
        ((N.choose m : ℝ) * (L.choose m : ℝ) *
          (((7 * m).choose (4 * m) : ℝ) / (((4 * N).choose (4 * m) : ℝ)))))
        < 1 := by
    calc
      (∑ m ∈ Finset.Icc 1 A,
        ((N.choose m : ℝ) * (L.choose m : ℝ) *
          (((7 * m).choose (4 * m) : ℝ) / (((4 * N).choose (4 * m) : ℝ)))))
          ≤ (1 / 20 : ℝ) / (1 - 1 / 20) + (N : ℝ) * B := hsum_le
      _ < 1 := by norm_num; linarith
  simpa [N, L, A] using hsum_final

theorem tail_bound_E₃_simplified :
    Real.exp 2 * ((7 / 2 : ℝ) ^ 3) * ((1 / 100 : ℝ) ^ 2) < 1 / 20 := by
  have h := tail_bound_real_E₃
  norm_num at h ⊢
  exact h

theorem small_term_E₃
    (N L m : ℕ) (hN : 0 < N) (hm : 0 < m) (hmN : m ≤ N) (hmL : m ≤ L)
    (hNL : 4 * N = 14 * L) (hLreal : (L : ℝ) = (2 / 7 : ℝ) * (N : ℝ))
    (hsmall : (m : ℝ) / (N : ℝ) ≤ 1 / 100) :
    (N.choose m : ℝ) * (L.choose m : ℝ) *
        ((14 * m).choose (4 * m) : ℝ) / ((4 * N).choose (4 * m) : ℝ)
      ≤ ((1 / 20 : ℝ) ^ m) := by
  have hcmN : 14 * m ≤ 4 * N := by
    simp_all
  have hraw := pippenger_small_term_raw N L 4 14 m hm hmN hmL (by norm_num) hcmN
  refine le_trans hraw ?_
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hbase_eq :
      (Real.exp 1 * (N : ℝ) / (m : ℝ) *
          (Real.exp 1 * (L : ℝ) / (m : ℝ)) *
          (((14 * m : ℕ) : ℝ) / ((4 * N : ℕ) : ℝ)) ^ 4)
        =
      Real.exp 2 * ((7 / 2 : ℝ) ^ 3) * (((m : ℝ) / (N : ℝ)) ^ 2) := by
    rw [hLreal]
    rw [show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
    norm_num [Nat.cast_mul]
    field_simp [hm_ne, hN_ne]
    ring
  have hx_nonneg : 0 ≤ (m : ℝ) / (N : ℝ) := by positivity
  have hx2_le : ((m : ℝ) / (N : ℝ)) ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ hx_nonneg hsmall 2
  have hbase_le : Real.exp 2 * ((7 / 2 : ℝ) ^ 3) *
      (((m : ℝ) / (N : ℝ)) ^ 2) ≤ 1 / 20 := by
    have hcoef_nonneg : 0 ≤ Real.exp 2 * ((7 / 2 : ℝ) ^ 3) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hx2_le hcoef_nonneg
    nlinarith [tail_bound_E₃_simplified, hmul]
  rw [hbase_eq]
  exact pow_le_pow_left₀ (by positivity) hbase_le m

theorem bad_ratio_sum_E₃_core (t : ℕ) (ht : 0 < t)
    (hdec : 50 * (((8750 * t : ℕ) : ℝ) ^ 2) *
        Real.exp (-(1 / 500 : ℝ) * ((8750 * t : ℕ) : ℝ)) < 1 / 2) :
    (∑ m ∈ Finset.Icc 1 (1316 * t),
      ((17500 * t).choose m : ℝ) * ((5000 * t).choose m : ℝ) *
        (((14 * m).choose (4 * m) : ℝ) / (((4 * (17500 * t)).choose (4 * m) : ℝ)))) < 1 := by
  let N := 17500 * t
  let L := 5000 * t
  let A := 1316 * t
  let D := 175 * t
  let B : ℝ := (((4 * N : ℕ) : ℝ) + 1) * Real.exp (-(N : ℝ) / 1000)
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hsum_le :
      (∑ m ∈ Finset.Icc 1 A,
        ((N.choose m : ℝ) * (L.choose m : ℝ) *
          (((14 * m).choose (4 * m) : ℝ) / (((4 * N).choose (4 * m) : ℝ)))))
        ≤ (1 / 20 : ℝ) / (1 - 1 / 20) + (N : ℝ) * B := by
    apply bad_sum_split A D N
      (fun m => ((N.choose m : ℝ) * (L.choose m : ℝ) *
          (((14 * m).choose (4 * m) : ℝ) / (((4 * N).choose (4 * m) : ℝ)))))
      (1 / 20) B
    · norm_num
    · norm_num
    · dsimp [B]; positivity
    · dsimp [A, N]
      simp_all
    · intro m hmI hmD
      have hmpos : 0 < m := (Finset.mem_Icc.mp hmI).1
      have hmA : m ≤ A := (Finset.mem_Icc.mp hmI).2
      have hmN : m ≤ N := by dsimp [A, N] at hmA ⊢; nlinarith
      have hmL : m ≤ L := by dsimp [A, L] at hmA ⊢; nlinarith
      have hsmall : (m : ℝ) / (N : ℝ) ≤ 1 / 100 := by
        rw [div_le_iff₀ (by exact_mod_cast hNpos)]
        have hmD' : (m : ℝ) ≤ (D : ℝ) := by exact_mod_cast hmD
        dsimp [D, N] at hmD' ⊢
        norm_num [Nat.cast_mul] at hmD' ⊢
        nlinarith
      have hs := small_term_E₃ N L m hNpos hmpos hmN hmL
        (by dsimp [N, L]; ring)
        (by dsimp [N, L]; norm_num [Nat.cast_mul]; ring)
        hsmall
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hs
    · intro m hmI hDm
      have hmpos : 0 < m := (Finset.mem_Icc.mp hmI).1
      have hmA : m ≤ A := (Finset.mem_Icc.mp hmI).2
      have hmN : m < N := by dsimp [A, N] at hmA ⊢; nlinarith [ht]
      have hmL : m < L := by dsimp [A, L] at hmA ⊢; nlinarith [ht]
      have hx_low : 1 / 100 ≤ (m : ℝ) / (N : ℝ) := by
        rw [le_div_iff₀ (by exact_mod_cast hNpos)]
        have hDm' : (D : ℝ) < (m : ℝ) := by exact_mod_cast hDm
        dsimp [D, N] at hDm' ⊢
        norm_num [Nat.cast_mul] at hDm' ⊢
        nlinarith
      have hx_high : (m : ℝ) / (N : ℝ) ≤ 47 / 625 := by
        rw [div_le_iff₀ (by exact_mod_cast hNpos)]
        have hmA' : (m : ℝ) ≤ (A : ℝ) := by exact_mod_cast hmA
        dsimp [A, N] at hmA' ⊢
        norm_num [Nat.cast_mul] at hmA' ⊢
        nlinarith
      have hphi := Phi_margin_E₃ ((m : ℝ) / (N : ℝ)) hx_low hx_high
      have hmterm := pippenger_mid_term_le N L 4 14 m (2 / 7 : ℝ)
        hNpos hmpos hmN hmL (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by dsimp [N, L]; norm_num [Nat.cast_mul]; ring)
        (by norm_num)
        hphi
      simpa [B, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmterm
  have hmid_small : (N : ℝ) * B < 1 / 2 := by
    have hpoly : (N : ℝ) * (((4 * N : ℕ) : ℝ) + 1) ≤
        50 * (((8750 * t : ℕ) : ℝ) ^ 2) := by
      dsimp [N]
      norm_num [Nat.cast_mul]
      have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
      nlinarith [sq_nonneg (t : ℝ), htR, ht1]
    have hexp_eq :
        Real.exp (-(N : ℝ) / 1000) =
          Real.exp (-(1 / 500 : ℝ) * ((8750 * t : ℕ) : ℝ)) := by
      dsimp [N]
      norm_num [Nat.cast_mul]
      ring_nf
    dsimp [B]
    rw [hexp_eq]
    calc
      (N : ℝ) * ((((4 * N : ℕ) : ℝ) + 1) *
          Real.exp (-(1 / 500 : ℝ) * ((8750 * t : ℕ) : ℝ)))
          = (N : ℝ) * (((4 * N : ℕ) : ℝ) + 1) *
          Real.exp (-(1 / 500 : ℝ) * ((8750 * t : ℕ) : ℝ)) := by ring
      _ ≤ 50 * (((8750 * t : ℕ) : ℝ) ^ 2) *
          Real.exp (-(1 / 500 : ℝ) * ((8750 * t : ℕ) : ℝ)) := by
            exact mul_le_mul_of_nonneg_right hpoly (by positivity)
      _ < 1 / 2 := hdec
  have hsum_final :
      (∑ m ∈ Finset.Icc 1 A,
        ((N.choose m : ℝ) * (L.choose m : ℝ) *
          (((14 * m).choose (4 * m) : ℝ) / (((4 * N).choose (4 * m) : ℝ)))))
        < 1 := by
    calc
      (∑ m ∈ Finset.Icc 1 A,
        ((N.choose m : ℝ) * (L.choose m : ℝ) *
          (((14 * m).choose (4 * m) : ℝ) / (((4 * N).choose (4 * m) : ℝ)))))
          ≤ (1 / 20 : ℝ) / (1 - 1 / 20) + (N : ℝ) * B := hsum_le
      _ < 1 := by norm_num; linarith
  simpa [N, L, A] using hsum_final

theorem tail_bound_E₄_simplified :
    Real.exp 2 * ((11 / 5 : ℝ) ^ 4) * ((1 / 100 : ℝ) ^ 3) < 1 / 20 := by
  have h := tail_bound_real_E₄
  norm_num at h ⊢
  exact h

theorem small_term_E₄
    (N L m : ℕ) (hN : 0 < N) (hm : 0 < m) (hmN : m ≤ N) (hmL : m ≤ L)
    (hNL : 5 * N = 11 * L) (hLreal : (L : ℝ) = (5 / 11 : ℝ) * (N : ℝ))
    (hsmall : (m : ℝ) / (N : ℝ) ≤ 1 / 100) :
    (N.choose m : ℝ) * (L.choose m : ℝ) *
        ((11 * m).choose (5 * m) : ℝ) / ((5 * N).choose (5 * m) : ℝ)
      ≤ ((1 / 20 : ℝ) ^ m) := by
  have hcmN : 11 * m ≤ 5 * N := by
    simp_all
  have hraw := pippenger_small_term_raw N L 5 11 m hm hmN hmL (by norm_num) hcmN
  refine le_trans hraw ?_
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hbase_eq :
      (Real.exp 1 * (N : ℝ) / (m : ℝ) *
          (Real.exp 1 * (L : ℝ) / (m : ℝ)) *
          (((11 * m : ℕ) : ℝ) / ((5 * N : ℕ) : ℝ)) ^ 5)
        =
      Real.exp 2 * ((11 / 5 : ℝ) ^ 4) * (((m : ℝ) / (N : ℝ)) ^ 3) := by
    rw [hLreal]
    rw [show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
    norm_num [Nat.cast_mul]
    field_simp [hm_ne, hN_ne]
    ring
  have hx_nonneg : 0 ≤ (m : ℝ) / (N : ℝ) := by positivity
  have hx3_le : ((m : ℝ) / (N : ℝ)) ^ 3 ≤ (1 / 100 : ℝ) ^ 3 := by
    exact pow_le_pow_left₀ hx_nonneg hsmall 3
  have hbase_le : Real.exp 2 * ((11 / 5 : ℝ) ^ 4) *
      (((m : ℝ) / (N : ℝ)) ^ 3) ≤ 1 / 20 := by
    have hcoef_nonneg : 0 ≤ Real.exp 2 * ((11 / 5 : ℝ) ^ 4) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hx3_le hcoef_nonneg
    nlinarith [tail_bound_E₄_simplified, hmul]
  rw [hbase_eq]
  exact pow_le_pow_left₀ (by positivity) hbase_le m

theorem bad_ratio_sum_E₄_core (t : ℕ) (ht : 0 < t)
    (hdec : 50 * (((13750 * t : ℕ) : ℝ) ^ 2) *
        Real.exp (-(1 / 500 : ℝ) * ((13750 * t : ℕ) : ℝ)) < 1 / 2) :
    (∑ m ∈ Finset.Icc 1 (7238 * t),
      ((27500 * t).choose m : ℝ) * ((12500 * t).choose m : ℝ) *
        (((11 * m).choose (5 * m) : ℝ) / (((5 * (27500 * t)).choose (5 * m) : ℝ)))) < 1 := by
  let N := 27500 * t
  let L := 12500 * t
  let A := 7238 * t
  let D := 275 * t
  let B : ℝ := (((5 * N : ℕ) : ℝ) + 1) * Real.exp (-(N : ℝ) / 1000)
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hsum_le :
      (∑ m ∈ Finset.Icc 1 A,
        ((N.choose m : ℝ) * (L.choose m : ℝ) *
          (((11 * m).choose (5 * m) : ℝ) / (((5 * N).choose (5 * m) : ℝ)))))
        ≤ (1 / 20 : ℝ) / (1 - 1 / 20) + (N : ℝ) * B := by
    apply bad_sum_split A D N
      (fun m => ((N.choose m : ℝ) * (L.choose m : ℝ) *
          (((11 * m).choose (5 * m) : ℝ) / (((5 * N).choose (5 * m) : ℝ)))))
      (1 / 20) B
    · norm_num
    · norm_num
    · dsimp [B]; positivity
    · dsimp [A, N]
      simp_all
    · intro m hmI hmD
      have hmpos : 0 < m := (Finset.mem_Icc.mp hmI).1
      have hmA : m ≤ A := (Finset.mem_Icc.mp hmI).2
      have hmN : m ≤ N := by dsimp [A, N] at hmA ⊢; nlinarith
      have hmL : m ≤ L := by dsimp [A, L] at hmA ⊢; nlinarith
      have hsmall : (m : ℝ) / (N : ℝ) ≤ 1 / 100 := by
        rw [div_le_iff₀ (by exact_mod_cast hNpos)]
        have hmD' : (m : ℝ) ≤ (D : ℝ) := by exact_mod_cast hmD
        dsimp [D, N] at hmD' ⊢
        norm_num [Nat.cast_mul] at hmD' ⊢
        nlinarith
      have hs := small_term_E₄ N L m hNpos hmpos hmN hmL
        (by dsimp [N, L]; ring)
        (by dsimp [N, L]; norm_num [Nat.cast_mul]; ring)
        hsmall
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hs
    · intro m hmI hDm
      have hmpos : 0 < m := (Finset.mem_Icc.mp hmI).1
      have hmA : m ≤ A := (Finset.mem_Icc.mp hmI).2
      have hmN : m < N := by dsimp [A, N] at hmA ⊢; nlinarith [ht]
      have hmL : m < L := by dsimp [A, L] at hmA ⊢; nlinarith [ht]
      have hx_low : 1 / 100 ≤ (m : ℝ) / (N : ℝ) := by
        rw [le_div_iff₀ (by exact_mod_cast hNpos)]
        have hDm' : (D : ℝ) < (m : ℝ) := by exact_mod_cast hDm
        dsimp [D, N] at hDm' ⊢
        norm_num [Nat.cast_mul] at hDm' ⊢
        nlinarith
      have hx_high : (m : ℝ) / (N : ℝ) ≤ 329 / 1250 := by
        rw [div_le_iff₀ (by exact_mod_cast hNpos)]
        have hmA' : (m : ℝ) ≤ (A : ℝ) := by exact_mod_cast hmA
        dsimp [A, N] at hmA' ⊢
        norm_num [Nat.cast_mul] at hmA' ⊢
        nlinarith
      have hphi := Phi_margin_E₄ ((m : ℝ) / (N : ℝ)) hx_low hx_high
      have hmterm := pippenger_mid_term_le N L 5 11 m (5 / 11 : ℝ)
        hNpos hmpos hmN hmL (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by dsimp [N, L]; norm_num [Nat.cast_mul]; ring)
        (by norm_num)
        hphi
      simpa [B, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmterm
  have hmid_small : (N : ℝ) * B < 1 / 2 := by
    have hpoly : (N : ℝ) * (((5 * N : ℕ) : ℝ) + 1) ≤
        50 * (((13750 * t : ℕ) : ℝ) ^ 2) := by
      dsimp [N]
      norm_num [Nat.cast_mul]
      have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
      nlinarith [sq_nonneg (t : ℝ), htR, ht1]
    have hexp_eq :
        Real.exp (-(N : ℝ) / 1000) =
          Real.exp (-(1 / 500 : ℝ) * ((13750 * t : ℕ) : ℝ)) := by
      dsimp [N]
      norm_num [Nat.cast_mul]
      ring_nf
    dsimp [B]
    rw [hexp_eq]
    calc
      (N : ℝ) * ((((5 * N : ℕ) : ℝ) + 1) *
          Real.exp (-(1 / 500 : ℝ) * ((13750 * t : ℕ) : ℝ)))
          = (N : ℝ) * (((5 * N : ℕ) : ℝ) + 1) *
          Real.exp (-(1 / 500 : ℝ) * ((13750 * t : ℕ) : ℝ)) := by ring
      _ ≤ 50 * (((13750 * t : ℕ) : ℝ) ^ 2) *
          Real.exp (-(1 / 500 : ℝ) * ((13750 * t : ℕ) : ℝ)) := by
            exact mul_le_mul_of_nonneg_right hpoly (by positivity)
      _ < 1 / 2 := hdec
  have hsum_final :
      (∑ m ∈ Finset.Icc 1 A,
        ((N.choose m : ℝ) * (L.choose m : ℝ) *
          (((11 * m).choose (5 * m) : ℝ) / (((5 * N).choose (5 * m) : ℝ)))))
        < 1 := by
    calc
      (∑ m ∈ Finset.Icc 1 A,
        ((N.choose m : ℝ) * (L.choose m : ℝ) *
          (((11 * m).choose (5 * m) : ℝ) / (((5 * N).choose (5 * m) : ℝ)))))
          ≤ (1 / 20 : ℝ) / (1 - 1 / 20) + (N : ℝ) * B := hsum_le
      _ < 1 := by norm_num; linarith
  simpa [N, L, A] using hsum_final

theorem pippenger_row_E₁ : StrongExpandersExist α₁ 4 (1 / 3) := by
  refine ⟨15000, by norm_num, ?_⟩
  have hdec_event := exp_decay_beats_poly_const 50 (1 / 500 : ℝ) (by norm_num)
  filter_upwards [hdec_event, Filter.eventually_atTop.2 ⟨1, fun k hk => hk⟩] with k hdec hkpos
  intro hdiv
  rcases hdiv with ⟨t, rfl⟩
  have ht : 0 < t := by omega
  have hdec_t : 50 * (((15000 * t : ℕ) : ℝ) ^ 2) *
        Real.exp (-(1 / 500 : ℝ) * ((15000 * t : ℕ) : ℝ)) < 1 / 2 := by
    simpa [Nat.cast_mul] using hdec
  have hsum := bad_ratio_sum_E₁_core t ht hdec_t
  have hsum' :
      (∑ m ∈ Finset.Icc 1 (3009 * t),
        ((30000 * t).choose m : ℝ) * ((10000 * t).choose m : ℝ) *
          ((12 * m).choose (4 * m) : ℝ) / (((4 * (30000 * t)).choose (4 * m) : ℝ))) < 1 := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hsum
  obtain ⟨edge, hcov, hexp⟩ :=
    good_matching_exists_of_ratio_sum_lt_one
      (30000 * t) (10000 * t) 4 12 (3009 * t)
      (by positivity) (by positivity) (by norm_num) (by norm_num)
      (by ring) (by nlinarith) hsum'
  refine ⟨finiteExpanderOfGoodEdge (30000 * t) (10000 * t) 4 (3009 * t)
      (by positivity) edge hcov hexp, ?_, ?_, ?_⟩
  · change @Fintype.card (Fin (30000 * t)) inferInstance = 2 * (15000 * t)
    simp
    ring
  · simp only [finiteExpanderOfGoodEdge]
    norm_num [Nat.cast_mul]
    change ((@Fintype.card (Fin (10000 * t)) inferInstance : ℕ) : ℚ) =
      (2 / 3 : ℚ) * (15000 * (t : ℚ))
    simp
    ring
  · simp only [finiteExpanderOfGoodEdge, α₁, Nat.cast_mul, Nat.cast_ofNat]
    have hceil : (2 : ℚ) * (1003 / 10000) * (15000 * (t : ℚ)) =
        ((3009 * t : ℕ) : ℚ) := by
      norm_num [Nat.cast_mul]
      ring
    rw [hceil, Nat.ceil_natCast]

theorem pippenger_row_E₂ : StrongExpandersExist (3009 / 10000) 4 (4 / 7) := by
  refine ⟨35000, by norm_num, ?_⟩
  have hdec_event := exp_decay_beats_poly_const 50 (1 / 500 : ℝ) (by norm_num)
  filter_upwards [hdec_event, Filter.eventually_atTop.2 ⟨1, fun k hk => hk⟩] with k hdec hkpos
  intro hdiv
  rcases hdiv with ⟨t, rfl⟩
  have ht : 0 < t := by omega
  have hdec_t : 50 * (((35000 * t : ℕ) : ℝ) ^ 2) *
        Real.exp (-(1 / 500 : ℝ) * ((35000 * t : ℕ) : ℝ)) < 1 / 2 := by
    simpa [Nat.cast_mul] using hdec
  have hsum := bad_ratio_sum_E₂_core t ht hdec_t
  have hsum' :
      (∑ m ∈ Finset.Icc 1 (21063 * t),
        ((70000 * t).choose m : ℝ) * ((40000 * t).choose m : ℝ) *
          ((7 * m).choose (4 * m) : ℝ) / (((4 * (70000 * t)).choose (4 * m) : ℝ))) < 1 := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hsum
  obtain ⟨edge, hcov, hexp⟩ :=
    good_matching_exists_of_ratio_sum_lt_one
      (70000 * t) (40000 * t) 4 7 (21063 * t)
      (by positivity) (by positivity) (by norm_num) (by norm_num)
      (by ring) (by nlinarith) hsum'
  refine ⟨finiteExpanderOfGoodEdge (70000 * t) (40000 * t) 4 (21063 * t)
      (by positivity) edge hcov hexp, ?_, ?_, ?_⟩
  · change @Fintype.card (Fin (70000 * t)) inferInstance = 2 * (35000 * t)
    simp
    ring
  · simp only [finiteExpanderOfGoodEdge]
    norm_num [Nat.cast_mul]
    change ((@Fintype.card (Fin (40000 * t)) inferInstance : ℕ) : ℚ) =
      (8 / 7 : ℚ) * (35000 * (t : ℚ))
    simp
    ring
  · simp only [finiteExpanderOfGoodEdge, Nat.cast_mul, Nat.cast_ofNat]
    have hceil : (2 : ℚ) * (3009 / 10000) * (35000 * (t : ℚ)) =
        ((21063 * t : ℕ) : ℚ) := by
      norm_num [Nat.cast_mul]
      ring
    rw [hceil, Nat.ceil_natCast]

theorem pippenger_row_E₃ : StrongExpandersExist α₂ 4 (2 / 7) := by
  refine ⟨8750, by norm_num, ?_⟩
  have hdec_event := exp_decay_beats_poly_const 50 (1 / 500 : ℝ) (by norm_num)
  filter_upwards [hdec_event, Filter.eventually_atTop.2 ⟨1, fun k hk => hk⟩] with k hdec hkpos
  intro hdiv
  rcases hdiv with ⟨t, rfl⟩
  have ht : 0 < t := by omega
  have hdec_t : 50 * (((8750 * t : ℕ) : ℝ) ^ 2) *
        Real.exp (-(1 / 500 : ℝ) * ((8750 * t : ℕ) : ℝ)) < 1 / 2 := by
    simpa [Nat.cast_mul] using hdec
  have hsum := bad_ratio_sum_E₃_core t ht hdec_t
  have hsum' :
      (∑ m ∈ Finset.Icc 1 (1316 * t),
        ((17500 * t).choose m : ℝ) * ((5000 * t).choose m : ℝ) *
          ((14 * m).choose (4 * m) : ℝ) / (((4 * (17500 * t)).choose (4 * m) : ℝ))) < 1 := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hsum
  obtain ⟨edge, hcov, hexp⟩ :=
    good_matching_exists_of_ratio_sum_lt_one
      (17500 * t) (5000 * t) 4 14 (1316 * t)
      (by positivity) (by positivity) (by norm_num) (by norm_num)
      (by ring) (by nlinarith) hsum'
  refine ⟨finiteExpanderOfGoodEdge (17500 * t) (5000 * t) 4 (1316 * t)
      (by positivity) edge hcov hexp, ?_, ?_, ?_⟩
  · change @Fintype.card (Fin (17500 * t)) inferInstance = 2 * (8750 * t)
    simp
    ring
  · simp only [finiteExpanderOfGoodEdge]
    norm_num [Nat.cast_mul]
    change ((@Fintype.card (Fin (5000 * t)) inferInstance : ℕ) : ℚ) =
      (4 / 7 : ℚ) * (8750 * (t : ℚ))
    simp
    ring
  · simp only [finiteExpanderOfGoodEdge, α₂, Nat.cast_mul, Nat.cast_ofNat]
    have hceil : (2 : ℚ) * (47 / 625) * (8750 * (t : ℚ)) =
        ((1316 * t : ℕ) : ℚ) := by
      norm_num [Nat.cast_mul]
      ring
    rw [hceil, Nat.ceil_natCast]

theorem pippenger_row_E₄ : StrongExpandersExist (329 / 1250) 5 (5 / 11) := by
  refine ⟨13750, by norm_num, ?_⟩
  have hdec_event := exp_decay_beats_poly_const 50 (1 / 500 : ℝ) (by norm_num)
  filter_upwards [hdec_event, Filter.eventually_atTop.2 ⟨1, fun k hk => hk⟩] with k hdec hkpos
  intro hdiv
  rcases hdiv with ⟨t, rfl⟩
  have ht : 0 < t := by omega
  have hdec_t : 50 * (((13750 * t : ℕ) : ℝ) ^ 2) *
        Real.exp (-(1 / 500 : ℝ) * ((13750 * t : ℕ) : ℝ)) < 1 / 2 := by
    simpa [Nat.cast_mul] using hdec
  have hsum := bad_ratio_sum_E₄_core t ht hdec_t
  have hsum' :
      (∑ m ∈ Finset.Icc 1 (7238 * t),
        ((27500 * t).choose m : ℝ) * ((12500 * t).choose m : ℝ) *
          ((11 * m).choose (5 * m) : ℝ) / (((5 * (27500 * t)).choose (5 * m) : ℝ))) < 1 := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hsum
  obtain ⟨edge, hcov, hexp⟩ :=
    good_matching_exists_of_ratio_sum_lt_one
      (27500 * t) (12500 * t) 5 11 (7238 * t)
      (by positivity) (by positivity) (by norm_num) (by norm_num)
      (by ring) (by nlinarith) hsum'
  refine ⟨finiteExpanderOfGoodEdge (27500 * t) (12500 * t) 5 (7238 * t)
      (by positivity) edge hcov hexp, ?_, ?_, ?_⟩
  · change @Fintype.card (Fin (27500 * t)) inferInstance = 2 * (13750 * t)
    simp
    ring
  · simp only [finiteExpanderOfGoodEdge]
    norm_num [Nat.cast_mul]
    change ((@Fintype.card (Fin (12500 * t)) inferInstance : ℕ) : ℚ) =
      (10 / 11 : ℚ) * (13750 * (t : ℚ))
    simp
    ring
  · simp only [finiteExpanderOfGoodEdge, Nat.cast_mul, Nat.cast_ofNat]
    have hceil : (2 : ℚ) * (329 / 1250) * (13750 * (t : ℚ)) =
        ((7238 * t : ℕ) : ℚ) := by
      norm_num [Nat.cast_mul]
      ring
    rw [hceil, Nat.ceil_natCast]

/-! ## Combined expander existence -/

/-- The four expander existence claims, proved by row-specific Pippenger constructions. -/
theorem pippenger_required_expanders :
    StrongExpandersExist α₁ 4 (1 / 3) ∧
    StrongExpandersExist (3009 / 10000) 4 (4 / 7) ∧
    StrongExpandersExist α₂ 4 (2 / 7) ∧
    StrongExpandersExist (329 / 1250) 5 (5 / 11) :=
  ⟨pippenger_row_E₁, pippenger_row_E₂, pippenger_row_E₃, pippenger_row_E₄⟩

end KaltonRoberts
