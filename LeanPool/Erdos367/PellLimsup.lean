/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/

import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Cases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify
import Aesop

/-!
# Erdős Problem #367: Consecutive Powerful Parts

We prove that `limsup_{n→∞} B₂(n)·B₂(n+1)·B₂(n+2) / (n²·log n) = ∞`,
where `B₂(m) = ∏_{p^e ∥ m, e≥2} p^e` is the powerful (2-full) part of `m`.

Equivalently (the cofinal form, which is what makes it a `limsup` rather than a
mere `sup`): `∀ M : ℝ, ∀ N : ℕ, ∃ n ≥ N, B₂(n) * B₂(n+1) * B₂(n+2) > M * n² * log n`,
i.e. the ratio exceeds every `M` for arbitrarily large `n`.

## Strategy

We use the Pell equation `x² - 8y² = 1` (fundamental solution `(3,1)`) to produce triples
`(n, n+1, n+2)` where `n = 8y²` is powerful, `n+1 = x²` is powerful, and `n+2 = x²+1`
has a large powerful part thanks to the algebraic structure of `ℤ[√2]`.

## What is proved

All lemmas and theorems are fully proved with no `sorry` statements.
`#print axioms erdos367` shows only the three standard axioms:
`propext`, `Classical.choice`, `Quot.sound`.
-/

noncomputable section

namespace Erdos367

open Finsupp Nat

/-! ## Powerful part -/

/-- The powerful (2-full) part of `m`: `∏_{p^e ∥ m, e ≥ 2} p^e`. -/
def powerfulPart (m : ℕ) : ℕ :=
  m.factorization.prod (fun p e => if e ≥ 2 then p ^ e else 1)

/-- A number is *powerful* if every prime factor has exponent ≥ 2. -/
def IsPowerful (m : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ m → 2 ≤ m.factorization p

lemma powerfulPart_of_powerful {m : ℕ} (hm : m ≠ 0)
    (h : IsPowerful m) : powerfulPart m = m := by
  unfold powerfulPart
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hm]
  apply Finsupp.prod_congr
  intro p hp
  rw [Nat.support_factorization] at hp
  simp only [Nat.mem_primeFactors] at hp
  simp only [ge_iff_le, h p hp.1 hp.2.1, ite_true]

lemma isPowerful_sq {k : ℕ} (hk : k ≠ 0) : IsPowerful (k ^ 2) := by
  intro p hp hd
  rw [Nat.factorization_pow, Finsupp.coe_nsmul, Pi.smul_apply, smul_eq_mul]
  have hmem : k.factorization p ≠ 0 := by
    rw [← Finsupp.mem_support_iff, Nat.support_factorization, Nat.mem_primeFactors]
    exact ⟨hp, hp.dvd_of_dvd_pow hd, hk⟩
  omega

lemma powerfulPart_sq {k : ℕ} (hk : k ≠ 0) : powerfulPart (k ^ 2) = k ^ 2 :=
  powerfulPart_of_powerful (by positivity) (isPowerful_sq hk)

private lemma eight_factorization_ne_two (p : ℕ) (hp2 : p ≠ 2) :
    (8 : ℕ).factorization p = 0 := by
  rw [show (8 : ℕ) = 2 ^ 3 from by norm_num, Nat.factorization_pow, Finsupp.coe_nsmul,
      Pi.smul_apply, smul_eq_mul, Nat.prime_two.factorization, Finsupp.single_apply,
      if_neg (Ne.symm hp2), mul_zero]

lemma isPowerful_eight_mul_sq {y : ℕ} (hy : y ≠ 0) : IsPowerful (8 * y ^ 2) := by
  intro p hp hd
  rw [Nat.factorization_mul (by norm_num) (by positivity : y ^ 2 ≠ 0),
      Finsupp.coe_add, Pi.add_apply]
  by_cases hp2 : p = 2
  · subst hp2
    have : (8 : ℕ).factorization 2 = 3 := by
      rw [show (8:ℕ) = 2^3 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]; simp
    rw [this]; omega
  · rw [eight_factorization_ne_two p hp2, zero_add, Nat.factorization_pow,
        Finsupp.coe_nsmul, Pi.smul_apply, smul_eq_mul]
    have hpy : p ∣ y := by
      have hpy2 : p ∣ y ^ 2 := by
        rcases hp.dvd_mul.mp hd with h | h
        · exfalso
          have h8 : p ∣ 2 ^ 3 := by norm_num at h ⊢; exact h
          have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h8
          rcases Nat.prime_two.eq_one_or_self_of_dvd p h2 with h | h
          · exact hp.one_lt.ne' h
          · exact hp2 h
        · exact h
      exact hp.dvd_of_dvd_pow hpy2
    have hmem : y.factorization p ≠ 0 := by
      rw [← Finsupp.mem_support_iff, Nat.support_factorization, Nat.mem_primeFactors]
      exact ⟨hp, hpy, hy⟩
    omega

lemma powerfulPart_eight_mul_sq {y : ℕ} (hy : y ≠ 0) :
    powerfulPart (8 * y ^ 2) = 8 * y ^ 2 :=
  powerfulPart_of_powerful (by positivity) (isPowerful_eight_mul_sq hy)

/-
If `p` is prime and `p² ∣ m` (with `m ≠ 0`), then `p²` divides `powerfulPart m`.
-/
lemma powerfulPart_ge_of_prime_sq_dvd {m p : ℕ} (hm : m ≠ 0) (hp : p.Prime)
    (hd : p ^ 2 ∣ m) : p ^ 2 ∣ powerfulPart m := by
  unfold powerfulPart
  rw [Finsupp.prod, Nat.support_factorization]
  refine dvd_trans ?_
    (Finset.dvd_prod_of_mem _
      (Nat.mem_primeFactors.mpr ⟨hp, by
        have hp_dvd_sq : p ∣ p ^ 2 := by
          rw [pow_two]
          exact dvd_mul_right p p
        exact dvd_trans hp_dvd_sq hd, hm⟩))
  have hfactor : 2 ≤ m.factorization p := by
    have hle := (Nat.factorization_le_iff_dvd (pow_ne_zero 2 hp.ne_zero) hm).2 hd
    have := hle p
    simpa [Nat.Prime.factorization_pow hp] using this
  simp only [ge_iff_le, hfactor, ite_true]
  exact pow_dvd_pow p hfactor

/-! ## Pell sequence for x² - 8y² = 1 -/

/-- Joint recurrence for Pell solutions `(X_j, Y_j)` with `X_j² - 8·Y_j² = 1`. -/
def pellXY : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | j + 1 => let (x, y) := pellXY j; (3 * x + 8 * y, x + 3 * y)

/-- X component of Pell solutions for `x² - 8y² = 1`. -/
def pellX (j : ℕ) : ℤ := (pellXY j).1

/-- Y component of Pell solutions for `x² - 8y² = 1`. -/
def pellY (j : ℕ) : ℤ := (pellXY j).2

@[simp] lemma pellX_zero : pellX 0 = 1 := rfl
@[simp] lemma pellY_zero : pellY 0 = 0 := rfl

@[simp] lemma pellX_succ (j : ℕ) : pellX (j + 1) = 3 * pellX j + 8 * pellY j := by
  simp [pellX, pellY, pellXY]

@[simp] lemma pellY_succ (j : ℕ) : pellY (j + 1) = pellX j + 3 * pellY j := by
  simp [pellX, pellY, pellXY]

private theorem pellXY_pos_nonneg (j : ℕ) : 0 < pellX j ∧ 0 ≤ pellY j := by
  induction j with
  | zero => constructor <;> simp [pellX, pellY, pellXY]
  | succ n ih =>
    exact ⟨by simp; linarith [ih.1, ih.2], by simp; linarith [ih.1, ih.2]⟩

theorem pellX_pos (j : ℕ) : 0 < pellX j := (pellXY_pos_nonneg j).1
theorem pellY_nonneg (j : ℕ) : 0 ≤ pellY j := (pellXY_pos_nonneg j).2

theorem pellY_pos {j : ℕ} (hj : 0 < j) : 0 < pellY j := by
  cases j with
  | zero => omega
  | succ n => simp; linarith [pellX_pos n, pellY_nonneg n]

/-- **Pell identity.** `X_j² - 8·Y_j² = 1`. -/
theorem pell_identity (j : ℕ) : pellX j ^ 2 - 8 * pellY j ^ 2 = 1 := by
  induction j with
  | zero => simp
  | succ n ih => simp only [pellX_succ, pellY_succ]; nlinarith

/-- `pellY j ≤ pellX j` for all `j`. -/
theorem pellY_le_pellX (j : ℕ) : pellY j ≤ pellX j := by
  induction j with
  | zero => simp
  | succ n ih =>
    simp only [pellX_succ, pellY_succ]
    linarith [pellY_nonneg n, pellX_pos n]

/-- Lower bound: `j ≤ Y_j`. The Pell `Y`-sequence grows at least linearly, so the
witness index `j` can be pushed arbitrarily large. -/
theorem pellY_ge_self (j : ℕ) : (j : ℤ) ≤ pellY j := by
  induction j with
  | zero => simp
  | succ n ih =>
    simp only [pellY_succ, Nat.cast_succ]
    linarith [pellX_pos n]

/-- Upper bound: `pellX j ≤ 11 ^ j`. -/
theorem pellX_le_pow (j : ℕ) : pellX j ≤ 11 ^ j := by
  induction j with
  | zero => simp
  | succ n ih =>
    simp only [pellX_succ]
    calc 3 * pellX n + 8 * pellY n ≤ 3 * pellX n + 8 * pellX n := by
          linarith [pellY_le_pellX n]
      _ = 11 * pellX n := by ring
      _ ≤ 11 * 11 ^ n := by linarith
      _ = 11 ^ (n + 1) := by ring

/-! ## The triple (n_j, n_j + 1, n_j + 2) -/

/-- `n_j = 8 · Y_j²`, a powerful number for `j ≥ 1`. -/
def pellN (j : ℕ) : ℕ := (8 * pellY j ^ 2).toNat

lemma pellN_eq (j : ℕ) : (pellN j : ℤ) = 8 * pellY j ^ 2 := by
  unfold pellN
  rw [Int.toNat_of_nonneg]
  positivity [pellY_nonneg j]

lemma pellN_pos {j : ℕ} (hj : 0 < j) : 0 < pellN j := by
  have h : (0 : ℤ) < 8 * pellY j ^ 2 := by positivity [pellY_pos hj]
  have := pellN_eq j; omega

/-- Lower bound: `j ≤ n_j`. Since `n_j = 8·Y_j²` and `j ≤ Y_j`, the witness `n_j`
grows at least linearly, so it exceeds any prescribed threshold. -/
theorem pellN_ge_self (j : ℕ) : j ≤ pellN j := by
  have hY : (j : ℤ) ≤ pellY j := pellY_ge_self j
  have hYnn : (0 : ℤ) ≤ pellY j := pellY_nonneg j
  have heq := pellN_eq j
  have : (j : ℤ) ≤ pellN j := by nlinarith [sq_nonneg ((pellY j) - j)]
  exact_mod_cast this

/-- **L0.** `n_j + 1 = X_j²` (as natural numbers). -/
theorem L0 (j : ℕ) : pellN j + 1 = (pellX j).toNat ^ 2 := by
  have hx := pellX_pos j
  zify
  rw [pellN_eq, Int.toNat_of_nonneg (le_of_lt hx)]
  linarith [pell_identity j]

/-- **L1.** `B₂(n_j) = n_j` for `j ≥ 1`: `n_j = 8·Y_j²` is powerful. -/
theorem L1 {j : ℕ} (hj : 0 < j) : powerfulPart (pellN j) = pellN j := by
  have hypos : (0 : ℤ) < pellY j := pellY_pos hj
  have heq : pellN j = 8 * (pellY j).toNat ^ 2 := by
    have := pellN_eq j
    zify [Int.toNat_of_nonneg (le_of_lt hypos)]
    linarith
  rw [heq]
  exact powerfulPart_eight_mul_sq (by omega)

/-- **L2.** `B₂(n_j + 1) = n_j + 1`: `n_j + 1 = X_j²` is a perfect square. -/
theorem L2 (j : ℕ) : powerfulPart (pellN j + 1) = pellN j + 1 := by
  rw [L0]
  exact powerfulPart_sq (by have := pellX_pos j; omega)

/-- **L3.** `n_j + 2 = X_j² + 1`. -/
theorem L3 (j : ℕ) : pellN j + 2 = (pellX j).toNat ^ 2 + 1 := by
  have := L0 j; omega

/-- For `j ≥ 1`, the triple product simplifies using L1 and L2. -/
theorem product_lower_bound {j : ℕ} (hj : 0 < j) :
    powerfulPart (pellN j) * powerfulPart (pellN j + 1) * powerfulPart (pellN j + 2) =
    pellN j * (pellN j + 1) * powerfulPart (pellN j + 2) := by
  rw [L1 hj, L2]

/-! ## The algebraic BOOST

For a prime `p ≡ 5 mod 8`, the fundamental unit `α = 3 + √8` of `ℤ[√8]` satisfies
`α^{(p+1)/2·p} ≡ -1 mod p²` in `ℤ[√8]`. In concrete terms: with `L = (p+1)/2 · p`,
`pellX L ≡ -1 (mod p²)` and `pellY L ≡ 0 (mod p²)`.

**Proof sketch:** Since `p ≡ 5 mod 8`, `(2/p) = -1` (Legendre symbol), so `p` is inert
in `ℤ[√2]`. The Frobenius on `ℤ[√2]/p ≅ 𝔽_{p²}` sends `√2 ↦ -√2`, giving
`(1+√2)^p ≡ 1-√2 = -(1+√2)^{-1} (mod p)`, hence `α^{(p+1)/2} ≡ -1 (mod p)`.
Hensel lifting (via the structure of `(ℤ[√2]/p^a)×`) gives `α^{(p+1)/2·p} ≡ -1 (mod p²)`.
-/

-- === Step 1: α^j = ⟨pellX j, 2 * pellY j⟩ in ℤ√2 ===
lemma alpha_pow (j : ℕ) : (⟨3, 2⟩ : ℤ√2) ^ j = ⟨pellX j, 2 * pellY j⟩ := by
  induction j with
  | zero => simp [pellX, pellY, pellXY]; rfl
  | succ j ih =>
    simp only [pow_succ]
    rw [ih]
    ext <;> simp [pellX, pellY, pellXY, Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring

-- === Step 2: ε² = α ===
lemma eps_sq : (⟨1, 1⟩ : ℤ√2) ^ 2 = (⟨3, 2⟩ : ℤ√2) := by decide

/-
=== Step 3a: sqrtd^(2k+1) = ⟨0, 2^k⟩ ===
-/
lemma sqrtd_pow_odd (k : ℕ) :
    (Zsqrtd.sqrtd : ℤ√2) ^ (2 * k + 1) = ⟨0, (2 : ℤ) ^ k⟩ := by
  induction k <;> simp_all +decide only [Nat.mul_succ, pow_succ, pow_mul]
  ext <;> simp +decide
  ring

/-
=== Step 3b: Euler criterion for 2 mod p ===
When p ≡ 5 (mod 8), 2 is a QNR, so 2^(p/2) ≡ -1 (mod p)
-/
lemma euler_two_mod (p : ℕ) (hp : p.Prime) (hp5 : p % 8 = 5) :
    (p : ℤ) ∣ (2 : ℤ) ^ (p / 2) + 1 := by
  -- Use Legendre symbol to get $(2/p) = -1$.
  have h_legendre : (jacobiSym 2 p) = -1 := by
    have hp_odd : Odd p := hp.odd_of_ne_two <| by
      rintro rfl
      norm_num at hp5
    rw [jacobiSym.at_two hp_odd, ZMod.χ₈_nat_eq_if_mod_eight]
    have hp2 : p % 2 = 1 := Nat.odd_iff.mp hp_odd
    simp [hp2, hp5]
  -- By Euler's criterion, we have $2^{p/2} \equiv jacobiSym 2 p \pmod p$.
  have h_euler : 2 ^ (p / 2) ≡ jacobiSym 2 p [ZMOD p] := by
    haveI := Fact.mk hp; simp +decide [ ← ZMod.intCast_eq_intCast_iff, jacobiSym ] ;
    simp +decide [ Nat.primeFactorsList_prime hp, legendreSym.eq_pow ];
  simpa [ h_legendre ] using h_euler.symm.dvd

/-
=== Step 4: Frobenius - ε^p ≡ ⟨1, -1⟩ (mod p) componentwise ===
Uses freshman's dream: (1 + sqrtd)^p = 1 + sqrtd^p + p*(stuff)
and sqrtd^p = ⟨0, 2^(p/2)⟩ for odd p, and 2^(p/2) ≡ -1 (mod p)
-/
lemma frobenius_eps (p : ℕ) (hp : p.Prime) (hp5 : p % 8 = 5) :
    (p : ℤ) ∣ ((⟨1, 1⟩ : ℤ√2) ^ p).re - 1 ∧
    (p : ℤ) ∣ ((⟨1, 1⟩ : ℤ√2) ^ p).im + 1 := by
  -- By added_pow_prime_eq, we have ε^p = 1^p + sqrtd^p + p * 1 * sqrtd * S
  have h_eps_p : (Zsqrtd.mk 1 1 : ℤ√2) ^ p = 1 ^ p +
      (Zsqrtd.sqrtd : ℤ√2) ^ p +
      (p : ℤ) * (1 : ℤ√2) * (Zsqrtd.sqrtd : ℤ√2) *
        (∑ k ∈ Finset.Ioo 0 p,
          1 ^ (k - 1) * (Zsqrtd.sqrtd : ℤ√2) ^ (p - k - 1) *
            (((Nat.choose p k / p : ℕ) : ℤ) : ℤ√2)) := by
    rw [show (Zsqrtd.mk 1 1 : ℤ√2) = 1 + (Zsqrtd.sqrtd : ℤ√2) by
      ext <;> simp [Zsqrtd.sqrtd]]
    exact add_pow_prime_eq hp (1 : ℤ√2) (Zsqrtd.sqrtd : ℤ√2)
  -- By sqrtd_pow_odd, we have sqrtd^p = ⟨0, 2^(p/2)⟩
  have h_sqrtd_p : (Zsqrtd.sqrtd : ℤ√2) ^ p = ⟨0, 2 ^ (p / 2)⟩ := by
    convert sqrtd_pow_odd ( p / 2 );
    omega;
  -- By euler_two_mod, we have p ∣ 2^(p/2) + 1
  have h_euler : (p : ℤ) ∣ 2 ^ (p / 2) + 1 := by
    convert euler_two_mod p hp hp5 using 1;
  simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ]

/-
=== Step 5: ε^(p+1) ≡ ⟨-1, 0⟩ (mod p) ===
ε^(p+1) = ε^p * ε, and ⟨1,-1⟩ * ⟨1,1⟩ = ⟨-1, 0⟩ in ℤ√2
-/
lemma eps_succ_mod (p : ℕ) (hp : p.Prime) (hp5 : p % 8 = 5) :
    (p : ℤ) ∣ ((⟨1, 1⟩ : ℤ√2) ^ (p + 1)).re + 1 ∧
    (p : ℤ) ∣ ((⟨1, 1⟩ : ℤ√2) ^ (p + 1)).im := by
  -- Use Frobenius to get the two components modulo `p`.
  obtain ⟨hr, hi⟩ :
      (p : ℤ) ∣ ((⟨1, 1⟩ : ℤ√2) ^ p).re - 1 ∧
        (p : ℤ) ∣ ((⟨1, 1⟩ : ℤ√2) ^ p).im + 1 := by
    convert frobenius_eps p hp hp5 using 1;
  simp only [pow_succ, Zsqrtd.re_mul, Zsqrtd.im_mul]
  constructor
  · rw [show ((⟨1, 1⟩ : ℤ√2) ^ p).re * 1 +
          2 * ((⟨1, 1⟩ : ℤ√2) ^ p).im * 1 + 1 =
        ((⟨1, 1⟩ : ℤ√2) ^ p).re - 1 +
          2 * (((⟨1, 1⟩ : ℤ√2) ^ p).im + 1) by ring]
    exact dvd_add hr (hi.mul_left 2)
  · rw [show ((⟨1, 1⟩ : ℤ√2) ^ p).re * 1 +
          ((⟨1, 1⟩ : ℤ√2) ^ p).im * 1 =
        ((⟨1, 1⟩ : ℤ√2) ^ p).re - 1 +
          (((⟨1, 1⟩ : ℤ√2) ^ p).im + 1) by ring]
    exact dvd_add hr hi

/-
=== Step 6: Hensel lift from mod p to mod p² ===
If z ≡ -1 (mod p) in ℤ√2 componentwise, then z^p ≡ -1 (mod p²)
Uses: z = -1 + (z+1), apply add_pow_prime_eq,
(-1)^p = -1 for odd p, and (z+1)^p, p*(z+1)*stuff have components div by p²
-/
lemma hensel_lift (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (z : ℤ√2)
    (hre : (p : ℤ) ∣ z.re + 1) (him : (p : ℤ) ∣ z.im) :
    ((p : ℤ) ^ 2 ∣ (z ^ p).re + 1) ∧ ((p : ℤ) ^ 2 ∣ (z ^ p).im) := by
  obtain ⟨k₁, hk₁⟩ := hre
  obtain ⟨k₂, hk₂⟩ := him
  have hz_re : z.re = -1 + p * k₁ := by linarith
  have hz_im : z.im = p * k₂ := by linarith
  -- Write $z = -1 + p \cdot w$ where $w = k₁ + k₂ \cdot \sqrt{2}$
  obtain ⟨w, hw⟩ : ∃ w : ℤ√2, z = -1 + (p : ℤ√2) * w := by
    exact ⟨⟨k₁, k₂⟩, by ext <;> simp [hz_re, hz_im]⟩
  -- Expand $(-1 + pw)^p$ using the binomial theorem.
  have h_expand :
      (-1 + (p : ℤ√2) * w) ^ p =
        (-1 : ℤ√2) ^ p + p * (-1 : ℤ√2) ^ (p - 1) * (p : ℤ√2) * w +
          ∑ k ∈ Finset.Icc 2 p,
            Nat.choose p k * (-1 : ℤ√2) ^ (p - k) * (p : ℤ√2) ^ k * w ^ k := by
    rw [add_comm, add_pow]
    erw [Finset.sum_Ico_eq_sub _]
    · norm_num [Finset.sum_range_succ]
      ring
    · linarith [hp.two_le]
  -- Since $p$ is odd, $(-1)^p = -1$ and $(-1)^{p-1} = 1$.
  have h_odd : (-1 : ℤ√2) ^ p = -1 ∧ (-1 : ℤ√2) ^ (p - 1) = 1 := by
    rcases hp.eq_two_or_odd' with rfl | ⟨m, rfl⟩
    · contradiction
    · constructor
      · simp [pow_succ, pow_mul]
      · simp [pow_mul]
  have h_sum_div :
      (p : ℤ√2) ^ 2 ∣
        ∑ k ∈ Finset.Icc 2 p,
          Nat.choose p k * (-1 : ℤ√2) ^ (p - k) * (p : ℤ√2) ^ k * w ^ k := by
    exact Finset.dvd_sum fun x hx =>
      dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right (pow_dvd_pow _ <| Finset.mem_Icc.mp hx |>.1) _)
        _
  obtain ⟨a, ha⟩ := h_sum_div
  simp_all +decide only [pow_succ, mul_assoc, mul_left_comm]
  exact ⟨⟨w.re + a.re, by simp; ring_nf⟩, ⟨w.im + a.im, by simp; ring_nf⟩⟩

/-
=== Main theorem ===
-/
lemma pell_boost (p : ℕ) (hp : p.Prime) (hp5 : p % 8 = 5) :
    let L := (p + 1) / 2 * p
    (p : ℤ) ^ 2 ∣ pellX L + 1 ∧ (p : ℤ) ^ 2 ∣ pellY L := by
  -- Let $L = (p+1)/2 * p$.
  set L := (p + 1) / 2 * p with hL;
  have h_div :
      (p : ℤ) ^ 2 ∣ ((⟨1, 1⟩ : ℤ√2) ^ (2 * L)).re + 1 ∧
        (p : ℤ) ^ 2 ∣ ((⟨1, 1⟩ : ℤ√2) ^ (2 * L)).im := by
    convert hensel_lift p hp ( by
      rintro rfl
      norm_num at hp5 ) ( ⟨ 1, 1 ⟩ ^ ( p + 1 ) ) _ _ using 1;
    · rw [← pow_mul, show 2 * L = (p + 1) * p by
        nlinarith [Nat.div_mul_cancel
          (show 2 ∣ p + 1 from Nat.dvd_of_mod_eq_zero (by omega))]]
    · rw [← pow_mul, show 2 * L = (p + 1) * p by
        nlinarith [Nat.div_mul_cancel
          (show 2 ∣ p + 1 from even_iff_two_dvd.mp (by
            simpa [parity_simps] using hp.eq_two_or_odd'.resolve_left (by
              rintro rfl
              norm_num at hp5)))]]
    · exact eps_succ_mod p hp hp5 |>.1;
    · exact eps_succ_mod p hp hp5 |>.2;
  -- By alpha_pow, α^L = ⟨pellX L, 2*pellY L⟩.
  have h_alpha_pow : (⟨1, 1⟩ : ℤ√2) ^ (2 * L) = ⟨pellX L, 2 * pellY L⟩ := by
    convert alpha_pow L using 1;
    rw [ pow_mul ]; aesop;
  rw [h_alpha_pow] at h_div
  constructor
  · exact h_div.1
  refine Int.dvd_of_dvd_mul_right_of_gcd_one h_div.2 ?_
  exact_mod_cast Nat.Coprime.pow_left 2 (hp.coprime_iff_not_dvd.mpr fun h => by
    have := Nat.le_of_dvd (by decide) h
    interval_cases p <;> trivial)

/-! ## From BOOST to divisibility of n_j + 2 -/

/-- If `pellX L ≡ -1 (mod m)` and `pellY L ≡ 0 (mod m)` with `L` odd, then
`m ∣ 4·((pellX ((L+1)/2))² + 1)`. This uses the doubling formula for Pell sequences. -/
lemma pell_sq_plus_one_div (L : ℕ) (m : ℤ) (_hm : 0 < m)
    (hx : m ∣ pellX L + 1) (hy : m ∣ pellY L)
    (hL_odd : L % 2 = 1) :
    m ∣ 4 * (pellX ((L + 1) / 2) ^ 2 + 1) := by
  have h_double : pellX ((L + 1) / 2 * 2) = 2 * pellX ((L + 1) / 2) ^ 2 - 1 := by
    have h_double : ∀ j : ℕ, pellX (2 * j) = 2 * pellX j ^ 2 - 1 := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have h_ind : ∀ j : ℕ, pellX (2 * j) = 2 * pellX j ^ 2 - 1 ∧
            pellY (2 * j) = 2 * pellX j * pellY j := by
          intro j; induction j with
          | zero => simp
          | succ j ih₂ =>
            simp only [Nat.mul_succ, pellX_succ, pellY_succ]
            constructor <;> [rw [ih₂.2]; rw [ih₂.2]] <;> nlinarith [pell_identity j]
        simp only [Nat.mul_succ, pellX_succ, pellY_succ]
        rw [h_ind j |>.2]; nlinarith [pell_identity j]
    rw [mul_comm, h_double]
  rw [show (L + 1) / 2 * 2 = L + 1 by omega] at h_double
  -- Now: 4*(pellX((L+1)/2)² + 1) = 2*(pellX(L+1) + 3) = 6*(pellX L + 1) + 16*pellY L
  have htarget :
      4 * (pellX ((L + 1) / 2) ^ 2 + 1) = 6 * (pellX L + 1) + 16 * pellY L := by
    rw [pellX_succ] at h_double
    linarith
  rw [htarget]
  exact dvd_add (hx.mul_left 6) (hy.mul_left 16)

/-
For a prime `p ≡ 5 mod 8`, setting `j = ((p+1)/2·p + 1) / 2`, we have
`p² ∣ pellN j + 2` (as integers).
-/
lemma prime_sq_dvd_pellN_plus2 (p : ℕ) (hp : p.Prime) (hp5 : p % 8 = 5) :
    let L := (p + 1) / 2 * p
    let j := (L + 1) / 2
    (p : ℤ) ^ 2 ∣ (pellN j + 2 : ℤ) := by
  obtain ⟨L, hL⟩ :
      ∃ L : ℕ, L = (p + 1) / 2 * p ∧
        (p : ℤ) ^ 2 ∣ pellX L + 1 ∧ (p : ℤ) ^ 2 ∣ pellY L := by
    exact ⟨ _, rfl, pell_boost p hp hp5 ⟩;
  obtain ⟨j, hj⟩ :
      ∃ j : ℕ, j = (L + 1) / 2 ∧ (p : ℤ) ^ 2 ∣ pellX j ^ 2 + 1 := by
    obtain ⟨j, hj⟩ :
        ∃ j : ℕ, j = (L + 1) / 2 ∧
          (p : ℤ) ^ 2 ∣ 4 * (pellX j ^ 2 + 1) := by
      refine ⟨_, rfl, ?_⟩
      exact pell_sq_plus_one_div L _ (sq_pos_of_pos (Nat.cast_pos.mpr hp.pos))
        hL.2.1 hL.2.2 (by
          norm_num [hL.1, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hp5]
          norm_num [← Nat.mod_mod_of_dvd p (by decide : 2 ∣ 8), hp5]
          omega)
    refine ⟨j, hj.1, ?_⟩
    refine Int.dvd_of_dvd_mul_right_of_gcd_one hj.2 ?_
    exact_mod_cast Nat.Coprime.pow_left 2 (hp.coprime_iff_not_dvd.mpr fun h => by
      have := Nat.le_of_dvd (by decide) h
      interval_cases p <;> trivial)
  -- Transfer divisibility from `pellX j ^ 2 + 1` to `pellN j + 2`.
  have h_div : (p : ℤ) ^ 2 ∣ pellN j + 2 := by
    convert hj.2 using 1;
    rw [pellN_eq, show pellX j ^ 2 = 8 * pellY j ^ 2 + 1 by
      linarith [pell_identity j]]
    ring
  aesop

/-! ## Key lemma and main theorem

### Assembly + Divergence (combined in `erdos367_key`)

Given a finite set `S` of primes `≡ 5 mod 8`, form
`L = lcm_{p∈S}((p+1)/2 · p)` (odd), set `j = (L+1)/2`. By a generalized BOOST
(extending `pell_boost` to odd multiples via `α^{kL₀} = (α^{L₀})^k ≡ (-1)^k`),
`p² ∣ n_j + 2` for each `p ∈ S`. Since the `p²` are coprime,
`B₂(n_j+2) ≥ ∏_{p∈S} p²`.

The ratio `∏ p² / log(n_j)` grows as `(1/log α) · ∏ 2p/(p+1) → ∞`,
since each factor `2p/(p+1) > 1` and there are infinitely many such primes
(Dirichlet: `Nat.setOf_prime_and_eq_mod_infinite` in Mathlib).
-/

/-! ### Helper lemmas for erdos367_key -/

/-
K1a: If `m ∣ z.re - 1` and `m ∣ z.im`, then for all `k`,
`m ∣ (z ^ k).re - 1` and `m ∣ (z ^ k).im`.
-/
lemma zsqrt2_pow_cong_one (m : ℤ) (z : ℤ√2) (k : ℕ)
    (hre : m ∣ z.re - 1) (him : m ∣ z.im) :
    m ∣ (z ^ k).re - 1 ∧ m ∣ (z ^ k).im := by
  induction k with
  | zero =>
    norm_num
  | succ k ih =>
    simp only [pow_succ, Zsqrtd.re_mul, Zsqrtd.im_mul]
    constructor
    · rw [show (z ^ k).re * z.re + 2 * (z ^ k).im * z.im - 1 =
          ((z ^ k).re - 1) * z.re + (z ^ k).im * (2 * z.im) + (z.re - 1) by
        ring]
      exact dvd_add
        (dvd_add (dvd_mul_of_dvd_left ih.1 z.re) (dvd_mul_of_dvd_left ih.2 (2 * z.im)))
        hre
    · rw [show (z ^ k).re * z.im + (z ^ k).im * z.re =
          ((z ^ k).re - 1) * z.im + (z ^ k).im * z.re + z.im by
        ring]
      exact dvd_add
        (dvd_add (dvd_mul_of_dvd_left ih.1 z.im) (dvd_mul_of_dvd_left ih.2 z.re))
        him

/-
K1b: If `m ∣ z.re + 1` and `m ∣ z.im` in `ℤ√2`,
and `t` is odd, then `m ∣ (z ^ t).re + 1` and `m ∣ (z ^ t).im`.
-/
lemma zsqrt2_odd_pow_neg_one (m : ℤ) (z : ℤ√2) (t : ℕ)
    (hre : m ∣ z.re + 1) (him : m ∣ z.im) (ht : t % 2 = 1) :
    m ∣ (z ^ t).re + 1 ∧ m ∣ (z ^ t).im := by
  rcases Nat.even_or_odd' t with ⟨k, rfl | rfl⟩
  · omega
  · simp only [pow_succ, pow_mul, pow_zero, one_mul, Zsqrtd.re_mul, Zsqrtd.im_mul]
    have hsq_re : m ∣ (z * z).re - 1 := by
      simp only [Zsqrtd.re_mul]
      rw [show z.re * z.re + 2 * z.im * z.im - 1 =
          (z.re + 1) * (z.re - 1) + z.im * (2 * z.im) by
        ring]
      exact dvd_add (dvd_mul_of_dvd_left hre (z.re - 1))
        (dvd_mul_of_dvd_left him (2 * z.im))
    have hsq_im : m ∣ (z * z).im := by
      simp only [Zsqrtd.im_mul]
      rw [show z.re * z.im + z.im * z.re = z.im * (2 * z.re) by ring]
      exact dvd_mul_of_dvd_left him (2 * z.re)
    have hpow := zsqrt2_pow_cong_one m (z * z) k hsq_re hsq_im
    constructor
    · rw [show ((z * z) ^ k).re * z.re + 2 * ((z * z) ^ k).im * z.im + 1 =
          (((z * z) ^ k).re - 1) * z.re + ((z * z) ^ k).im * (2 * z.im) +
            (z.re + 1) by
        ring]
      exact dvd_add
        (dvd_add (dvd_mul_of_dvd_left hpow.1 z.re)
          (dvd_mul_of_dvd_left hpow.2 (2 * z.im)))
        hre
    · exact dvd_add (dvd_mul_of_dvd_right him (((z * z) ^ k).re))
        (dvd_mul_of_dvd_left hpow.2 z.re)

/-
Generalized boost: for prime `p ≡ 5 mod 8`, if `M_p ∣ L` and `L` is odd,
then `p² ∣ pellN ((L+1)/2) + 2`.
-/
lemma generalized_boost_pellN (p : ℕ) (hp : p.Prime) (hp5 : p % 8 = 5)
    (L : ℕ) (hL_dvd : (p + 1) / 2 * p ∣ L) (hL_odd : L % 2 = 1) :
    p ^ 2 ∣ pellN ((L + 1) / 2) + 2 := by
  -- Let $M = (p + 1) / 2 * p$.
  set M := (p + 1) / 2 * p;
  -- Since $M \mid L$, we have $L = M * t$ for some integer $t$.
  obtain ⟨t, ht⟩ : ∃ t : ℕ, L = M * t := hL_dvd;
  -- By pell_boost, $(p : ℤ)^2 | pellX M + 1$ and $(p : ℤ)^2 | pellY M$.
  have h_boost : (p : ℤ)^2 ∣ pellX M + 1 ∧ (p : ℤ)^2 ∣ pellY M := by
    convert pell_boost p hp hp5 using 1;
  -- By zsqrt2_odd_pow_neg_one, $(p : ℤ)^2 | pellX L + 1$ and $(p : ℤ)^2 | pellY L$.
  have h_odd_pow : (p : ℤ)^2 ∣ pellX L + 1 ∧ (p : ℤ)^2 ∣ pellY L := by
    convert zsqrt2_odd_pow_neg_one
        (p ^ 2 : ℤ) (⟨3, 2⟩ ^ M) t _ _ _ using 1 <;>
      norm_num [ht]
    · rw [ ← pow_mul, alpha_pow ];
    · rw [ ← pow_mul, alpha_pow ]; norm_num [ pellX, pellY ];
      exact ⟨
        fun h => dvd_mul_of_dvd_right h _,
        fun h => by
          exact Int.dvd_of_dvd_mul_right_of_gcd_one h <| by
            exact_mod_cast Nat.Coprime.pow_left 2 <|
              hp.coprime_iff_not_dvd.mpr fun h => by
                have := Nat.le_of_dvd (by norm_num) h
                interval_cases p <;> trivial⟩
    · convert h_boost.1 using 1;
      exact congr_arg₂ _ ( congr_arg Zsqrtd.re ( alpha_pow M ) ) rfl;
    · rw [show ((⟨3, 2⟩ : ℤ√2) ^ M).im = 2 * pellY M
        from congr_arg Zsqrtd.im (alpha_pow M)]
      exact h_boost.2.mul_left 2
    · cases Nat.mod_two_eq_zero_or_one t <;> simp_all +decide [ Nat.mul_mod ];
  -- By pell_sq_plus_one_div, $(p : ℤ)^2 | 4 * (pellX ((L + 1) / 2)^2 + 1)$.
  have h_div : (p : ℤ)^2 ∣ 4 * (pellX ((L + 1) / 2)^2 + 1) := by
    convert pell_sq_plus_one_div L (p ^ 2) (pow_pos (Nat.cast_pos.mpr hp.pos) 2)
      h_odd_pow.1 h_odd_pow.2 hL_odd using 1
  -- Since $p$ is odd, we have $(p : ℤ)^2 \mid pellX ((L + 1) / 2)^2 + 1$.
  have h_div_odd : (p : ℤ)^2 ∣ pellX ((L + 1) / 2)^2 + 1 := by
    refine Int.dvd_of_dvd_mul_right_of_gcd_one h_div ?_
    exact_mod_cast Nat.Coprime.pow_left 2 (hp.coprime_iff_not_dvd.mpr fun h => by
      have := Nat.le_of_dvd (by decide) h
      interval_cases p <;> trivial)
  convert h_div_odd using 1;
  rw [ ← Int.natCast_dvd_natCast ]; norm_num [ L3 ];
  rw [ max_eq_left ( pellX_pos _ |> le_of_lt ) ]

/-- Infinitely many primes are ≡ 5 mod 8. -/
lemma infinite_primes_5_mod_8 : Set.Infinite {p : ℕ | p.Prime ∧ p % 8 = 5} := by
  have hinf : Set.Infinite {p : ℕ | p.Prime ∧ (p : ZMod 8) = 5} :=
    Nat.infinite_setOf_prime_and_eq_mod (by decide)
  apply hinf.mono
  intro p ⟨hp, hp5⟩
  refine ⟨hp, ?_⟩
  have : (p : ZMod 8) = ((5 : ℕ) : ZMod 8) := by exact_mod_cast hp5
  rw [ZMod.natCast_eq_natCast_iff'] at this
  omega

/-
From an infinite set, extract a finset of any desired cardinality.
-/
lemma exists_finset_of_infinite {α : Type*} {S : Set α} (hS : S.Infinite) (n : ℕ) :
    ∃ T : Finset α, n ≤ T.card ∧ ∀ x ∈ T, x ∈ S := by
  rcases hS.exists_subset_card_eq n with ⟨ T, hT ⟩; aesop

/-
For a finset of distinct primes, if each `p^2 ∣ m`, then `∏ p^2 ∣ m`.
-/
lemma finset_coprime_sq_dvd (S : Finset ℕ) (m : ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hdvd : ∀ p ∈ S, p ^ 2 ∣ m) :
    S.prod (fun p => p ^ 2) ∣ m := by
  induction S using Finset.induction with
  | empty => simp
  | insert p S hpS ih =>
      rw [Finset.prod_insert hpS]
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · exact Nat.Coprime.prod_right fun x hx =>
          Nat.Coprime.pow _ _ <|
            (hS p (Finset.mem_insert_self p S)).coprime_iff_not_dvd.mpr fun hpx_dvd =>
              hpS <| by
                have hpx := (Nat.prime_dvd_prime_iff_eq
                  (hS p (Finset.mem_insert_self p S))
                  (hS x (Finset.mem_insert_of_mem hx))).mp hpx_dvd
                simpa [hpx] using hx
      · exact hdvd p (Finset.mem_insert_self p S)
      · exact ih
          (fun q hq => hS q (Finset.mem_insert_of_mem hq))
          (fun q hq => hdvd q (Finset.mem_insert_of_mem hq))

/-
Upper bound: `pellN j < 11 ^ (2 * j)` for `j ≥ 1`.
-/
lemma pellN_lt_eleven_pow (j : ℕ) (_hj : 0 < j) : pellN j < 11 ^ (2 * j) := by
  rw [ pow_mul' ];
  rw [ show pellN j = ( pellX j |> Int.toNat ) ^ 2 - 1 from ?_ ];
  · rw [ tsub_lt_iff_left ];
    · exact lt_add_of_pos_of_le zero_lt_one
        (Nat.pow_le_pow_left (by
          linarith [pellX_le_pow j,
            Int.toNat_of_nonneg (show 0 ≤ pellX j from le_of_lt (pellX_pos j))]) 2)
    · exact Nat.one_le_pow _ _ (by
        linarith [pellX_pos j, Int.toNat_of_nonneg (le_of_lt (pellX_pos j))])
  · exact eq_tsub_of_add_eq ( L0 j )

/-
Product of `(p+1)/2 * p` is odd when all `p ≡ 5 mod 8`.
-/
lemma prod_Mp_odd (S : Finset ℕ) (hS : ∀ p ∈ S, p % 8 = 5) :
    S.prod (fun p => (p + 1) / 2 * p) % 2 = 1 := by
  rw [Finset.prod_nat_mod, Finset.prod_eq_one] <;> norm_num
  intro p hp
  rw [← Nat.mod_add_div p 8, hS p hp]
  norm_num [Nat.add_mod, Nat.mul_mod]
  omega

/-
Product of `(p+1)/2 * p` is positive when `S` is nonempty and elements are primes ≡ 5 mod 8.
-/
lemma prod_Mp_pos (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p % 8 = 5) (_hne : S.Nonempty) :
    0 < S.prod (fun p => (p + 1) / 2 * p) := by
  exact Finset.prod_pos fun p hp =>
    mul_pos
      (Nat.div_pos (by linarith [Nat.Prime.two_le (hS p hp |>.1)]) zero_lt_two)
      (Nat.Prime.pos (hS p hp |>.1))

/-
For `p ≥ 5`, `3 * p ^ 2 ≥ 5 * ((p + 1) / 2 * p)`.
-/
lemma ratio_bound_per_prime (p : ℕ) (hp : 5 ≤ p) (_hp_odd : p % 2 = 1) :
    5 * ((p + 1) / 2 * p) ≤ 3 * p ^ 2 := by
  nlinarith [ Nat.div_mul_le_self ( p + 1 ) 2 ]

/-
Product ratio bound: `(5/3)^|S| * ∏ M_p ≤ ∏ p²` ∈ ℕ,
or equivalently `5^|S| * ∏ M_p ≤ 3^|S| * ∏ p²`.
-/
lemma prod_ratio_bound_nat (S : Finset ℕ) (hS : ∀ p ∈ S, 5 ≤ p ∧ p % 2 = 1) :
    5 ^ S.card * S.prod (fun p => (p + 1) / 2 * p) ≤
    3 ^ S.card * S.prod (fun p => p ^ 2) := by
  induction S using Finset.induction with
  | empty => simp
  | insert p S hpS ih =>
      rw [Finset.card_insert_of_notMem hpS, Finset.prod_insert hpS, Finset.prod_insert hpS]
      simp only [pow_succ]
      convert Nat.mul_le_mul
        (ratio_bound_per_prime _ (hS p (Finset.mem_insert_self p S)).1
          (hS p (Finset.mem_insert_self p S)).2)
        (ih (fun q hq => hS q (Finset.mem_insert_of_mem hq))) using 1 <;> ring

/-
**Key lemma.** For every threshold `j₀` and every `N`, there exists `j ≥ j₀` (with
`j ≥ 1`) such that `powerfulPart(n_j + 2) > N · log(n_j)`. The lower bound `j₀`
lets the caller push the witness index — and hence `n_j` — arbitrarily large,
which is what turns the bound into a genuine `limsup = ∞` statement.
-/
lemma erdos367_key (j₀ : ℕ) :
    ∀ N : ℝ, ∃ j : ℕ, j₀ ≤ j ∧ 0 < j ∧
      (powerfulPart (pellN j + 2) : ℝ) > N * Real.log (pellN j : ℝ) := by
  intro N
  by_cases hN : N ≤ 0;
  · refine ⟨max 1 j₀, le_max_right _ _, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
    have hjpos : 0 < max 1 j₀ := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hlog : 0 ≤ Real.log (pellN (max 1 j₀) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast pellN_pos hjpos)
    refine lt_of_le_of_lt
      (mul_nonpos_of_nonpos_of_nonneg hN hlog) ?_
    exact_mod_cast (by
      unfold powerfulPart
      apply Finset.prod_pos
      intro p hp
      simp only [Nat.support_factorization, Nat.mem_primeFactors] at hp
      simp only [ge_iff_le]
      split_ifs with h
      · exact pow_pos hp.1.pos _
      · exact Nat.one_pos :
        0 < powerfulPart (pellN (max 1 j₀) + 2))
  · -- Choose s with (5/3:ℝ)^s > max 1 (2 * N * Real.log 11) using pow_unbounded_of_one_lt.
    obtain ⟨s, hs⟩ : ∃ s : ℕ, (5 / 3 : ℝ) ^ s > max 1 (2 * N * Real.log 11) := by
      exact pow_unbounded_of_one_lt _ <| by norm_num;
    -- Extract a finite set of primes `p ≡ 5 mod 8`, large enough to also force
    -- the witness index `j ≥ j₀` (we request `max s (2 * j₀)` of them).
    obtain ⟨S, hS_card_max, hS⟩ :
        ∃ S : Finset ℕ, max s (2 * j₀) ≤ S.card ∧ ∀ p ∈ S, p.Prime ∧ p % 8 = 5 := by
      exact Exists.elim (exists_finset_of_infinite infinite_primes_5_mod_8 (max s (2 * j₀)))
        fun S hS => ⟨S, hS.1, fun p hp => hS.2 p hp⟩
    have hS_card : s ≤ S.card := le_trans (le_max_left _ _) hS_card_max
    have hS_card_j : 2 * j₀ ≤ S.card := le_trans (le_max_right _ _) hS_card_max
    -- Set L := S.prod (fun p => (p + 1) / 2 * p) and j := (L + 1) / 2.
    set L := S.prod (fun p => (p + 1) / 2 * p) with hL_def
    set j := (L + 1) / 2 with hj_def
    -- Each prime factor contributes a factor ≥ 2, so `L ≥ 2 ^ |S| ≥ |S| ≥ 2·j₀`,
    -- hence `j = (L + 1) / 2 ≥ j₀`.
    have hj0_le : j₀ ≤ j := by
      have hfac : ∀ p ∈ S, 2 ≤ (p + 1) / 2 * p := by
        intro p hp
        have hp5 := (hS p hp).2
        have hp5le : 5 ≤ p := by
          rcases Nat.lt_or_ge p 5 with h | h
          · interval_cases p <;> omega
          · exact h
        have h1 : 3 ≤ (p + 1) / 2 := by omega
        calc 2 ≤ 3 * 5 := by norm_num
          _ ≤ (p + 1) / 2 * p := Nat.mul_le_mul h1 hp5le
      have h2card : 2 ^ S.card ≤ L := by
        calc 2 ^ S.card = ∏ _p ∈ S, 2 := by rw [Finset.prod_const]
          _ ≤ L := Finset.prod_le_prod' hfac
      have hcard_le : S.card ≤ 2 ^ S.card := Nat.lt_two_pow_self.le
      have hj0_le_L : 2 * j₀ ≤ L := le_trans hS_card_j (le_trans hcard_le h2card)
      omega
    -- Show L is odd and L > 0.
    have hL_odd : L % 2 = 1 := by
      exact prod_Mp_odd S fun p hp => hS p hp |>.2
    have hL_pos : 0 < L := by
      exact Finset.prod_pos fun p hp =>
        mul_pos
          (Nat.div_pos (by linarith [Nat.Prime.two_le (hS p hp |>.1)]) zero_lt_two)
          (Nat.Prime.pos (hS p hp |>.1))
    have hj_pos : 0 < j := by
      exact Nat.div_pos ( by linarith ) zero_lt_two
    have h_prod_sq_dvd : S.prod (fun p => p ^ 2) ∣ powerfulPart (pellN j + 2) := by
      apply finset_coprime_sq_dvd;
      · exact fun p hp => hS p hp |>.1;
      · intro p hp
        have h_div : p ^ 2 ∣ pellN j + 2 := by
          apply generalized_boost_pellN p (hS p hp).left (hS p hp).right L
            (Finset.dvd_prod_of_mem _ hp) hL_odd
        exact powerfulPart_ge_of_prime_sq_dvd (by linarith [pellN_pos hj_pos])
          (hS p hp |>.1) h_div
    have h_prod_sq_ge : (S.prod (fun p => p ^ 2) : ℝ) ≥ (5 / 3 : ℝ) ^ s * L := by
      have h_prod_sq_ge : (S.prod (fun p => p ^ 2) : ℝ) ≥
          (5 / 3 : ℝ) ^ S.card * L := by
        have h_prod_sq_ge :
            ∀ p ∈ S, (p ^ 2 : ℝ) ≥ (5 / 3 : ℝ) * (((p : ℝ) + 1) / 2 * p) := by
          intro p hp
          nlinarith only [show (p : ℝ) ≥ 5 by
            exact_mod_cast le_of_not_gt fun h => by
              have := hS p hp
              interval_cases p <;> trivial]
        have h_lower_nonneg :
            ∀ p ∈ S, 0 ≤ (5 / 3 : ℝ) * (((p : ℝ) + 1) / 2 * p) := by
          intro p hp
          positivity
        have h_lower_le_sq :
            (∏ p ∈ S, (5 / 3 : ℝ) * (((p : ℝ) + 1) / 2 * p)) ≤
              ∏ p ∈ S, (p : ℝ) ^ 2 :=
          Finset.prod_le_prod h_lower_nonneg h_prod_sq_ge
        have hL_le :
            (L : ℝ) ≤ ∏ p ∈ S, (((p : ℝ) + 1) / 2 * p) := by
          change ((S.prod (fun p => (p + 1) / 2 * p) : ℕ) : ℝ) ≤
            ∏ p ∈ S, (((p : ℝ) + 1) / 2 * p)
          rw [Nat.cast_prod]
          exact Finset.prod_le_prod (fun p hp => by positivity) fun p hp => by
            rw [Nat.cast_mul]
            have hdiv : (((p + 1) / 2 : ℕ) : ℝ) ≤ ((p : ℝ) + 1) / 2 := by
              rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2)]
              norm_cast
              exact Nat.div_mul_le_self (p + 1) 2
            exact mul_le_mul_of_nonneg_right hdiv (Nat.cast_nonneg p)
        have h_first :
            (5 / 3 : ℝ) ^ S.card * L ≤
              ∏ p ∈ S, (5 / 3 : ℝ) * (((p : ℝ) + 1) / 2 * p) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
          exact mul_le_mul_of_nonneg_left hL_le (by positivity)
        exact le_trans h_first h_lower_le_sq
      exact le_trans
          (mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ (by norm_num) hS_card)
            (Nat.cast_nonneg _))
          h_prod_sq_ge
    have h_log_bound : Real.log (pellN j) < (L + 1) * Real.log 11 := by
      have h_log_bound : Real.log (pellN j) < Real.log (11 ^ (2 * j)) := by
        exact Real.log_lt_log (Nat.cast_pos.mpr <| pellN_pos hj_pos) <|
            mod_cast pellN_lt_eleven_pow j hj_pos
      norm_num at *
      exact h_log_bound.trans_le
          (mul_le_mul_of_nonneg_right
            (by norm_cast; omega)
            (Real.log_nonneg (by norm_num)))
    have h_final_bound : (S.prod (fun p => p ^ 2) : ℝ) > 2 * N * Real.log 11 * L := by
      exact lt_of_lt_of_le
          (mul_lt_mul_of_pos_right
            (lt_of_le_of_lt (le_max_right _ _) hs)
            (Nat.cast_pos.mpr hL_pos))
          h_prod_sq_ge
    have h_final_ineq :
        (powerfulPart (pellN j + 2) : ℝ) > N * Real.log (pellN j) := by
      have h_final_ineq :
          (powerfulPart (pellN j + 2) : ℝ) ≥ (S.prod (fun p => p ^ 2) : ℝ) := by
        norm_cast
        refine Nat.le_of_dvd ?_ h_prod_sq_dvd
        exact Nat.pos_of_ne_zero (by
            exact Finsupp.prod_ne_zero_iff.mpr fun p hp => by aesop)
      nlinarith [
          show (L : ℝ) ≥ 1 by exact_mod_cast hL_pos,
          show (Real.log 11 : ℝ) > 0 by positivity,
          show (N : ℝ) > 0 by exact_mod_cast lt_of_not_ge hN,
          mul_le_mul_of_nonneg_left
            (show (L : ℝ) ≥ 1 by exact_mod_cast hL_pos)
            (show (0 : ℝ) ≤ N by exact_mod_cast le_of_not_ge hN)]
    use j, hj0_le, hj_pos, h_final_ineq

/-- **Main theorem (Erdős #367).** For every `M : ℝ` and every threshold `N : ℕ`,
there exists `n ≥ N` such that `B₂(n) · B₂(n+1) · B₂(n+2) > M · n² · log(n)`.

Because the bound holds for arbitrarily large `n`, this is the genuine
`limsup_{n→∞} B₂(n)·B₂(n+1)·B₂(n+2) / (n²·log n) = ∞`, not merely a supremum:
the ratio exceeds every `M` cofinally often. -/
theorem erdos367 :
    ∀ M : ℝ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      (powerfulPart n * powerfulPart (n + 1) * powerfulPart (n + 2) : ℝ) >
        M * (n : ℝ) ^ 2 * Real.log (n : ℝ) := by
  intro M N
  obtain ⟨j, hj0, hj, hbig⟩ := erdos367_key N M
  refine ⟨pellN j, le_trans hj0 (pellN_ge_self j), ?_⟩
  rw [show pellN j + 1 + 1 = pellN j + 2 from by ring, L1 hj, L2]
  have hnj_pos : (0 : ℝ) < pellN j := Nat.cast_pos.mpr (pellN_pos hj)
  have hcast : (↑(pellN j + 1) : ℝ) = ↑(pellN j) + 1 := by push_cast; ring
  rw [hcast]
  by_cases hM : 0 ≤ M * Real.log ↑(pellN j)
  · calc ↑(pellN j) * (↑(pellN j) + 1) * (↑(powerfulPart (pellN j + 2)) : ℝ)
        > ↑(pellN j) * (↑(pellN j) + 1) * (M * Real.log ↑(pellN j)) :=
          mul_lt_mul_of_pos_left hbig (by positivity)
      _ ≥ ↑(pellN j) ^ 2 * (M * Real.log ↑(pellN j)) := by
          nlinarith [sq_nonneg (↑(pellN j) : ℝ)]
      _ = M * ↑(pellN j) ^ 2 * Real.log ↑(pellN j) := by ring
  · push Not at hM
    have h1 : M * ↑(pellN j) ^ 2 * Real.log ↑(pellN j) < 0 := by
      have : (↑(pellN j) : ℝ) ^ 2 > 0 := by positivity
      nlinarith
    linarith [show (0 : ℝ) ≤ ↑(pellN j) * (↑(pellN j) + 1) *
      ↑(powerfulPart (pellN j + 2)) from by positivity]


end Erdos367

end
