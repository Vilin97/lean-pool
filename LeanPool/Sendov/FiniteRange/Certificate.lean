/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.FiniteRange.Batch
public import LeanPool.Sendov.FiniteRange.PackBridge

/-!
# Kernel-checked Bernstein certificates

Each batch file `Sendov.FiniteRange.Degree<n₀>_<n₁>` proves `R n α < 1` for `n₀ ≤ n ≤ n₁` by
bounding `R n α` through `Sendov.R_le_batch` by a rational function of `α`, and certifying that
the numerator of `1 - bound` is positive on the batch's `α`-range.  Upstream, each certificate
was an explicit polynomial identity closed by `ring` under a raised heartbeat budget, and the
rational bound was cleared by `field_simp` in every batch.  Here the same data are checked by
the kernel instead:

* `Sendov.bern p q d b` expands `∑ⱼ bⱼ Xʲ (p - q X)^(d-j)` into a coefficient list, so the
  statement "`p ^ d • P` has Bernstein coefficients `b` on `[0, p/q]`" is a decidable equality
  of lists, and `Sendov.pev_pos_of_bern` turns positive coefficients into positivity of `P`;
* `Sendov.batchP n₀ n₁ k L Nmom` computes the numerator polynomial directly from the batch
  parameters and the moment numerator, and `Sendov.batch_lt_one` proves once, for symbolic
  `n₀`, `n₁`, `k`, that positivity of this polynomial gives the batch bound `< 1`.

Numerals beyond 90 digits cannot sit on one line; `Sendov.big` assembles them from decimal
chunks.
-/

public section

namespace Sendov

/-- A large natural number assembled from little-endian chunks of at most 90 decimal
digits, as an integer. -/
@[expose]
def big (chunks : List ℕ) : ℤ := (npev chunks (10 ^ 90) : ℤ)

/-! ### Polynomial arithmetic on coefficient lists -/

/-- Scalar multiple of a dense integer polynomial. -/
@[expose]
def pscale (c : ℤ) (p : List ℤ) : List ℤ := p.map (fun a => c * a)

lemma pev_pscale (c : ℤ) (p : List ℤ) (x : ℝ) : pev (pscale c p) x = (c : ℝ) * pev p x :=
  pev_map_mul c p x

/-- Difference of dense integer polynomials. -/
@[expose]
def psub (p q : List ℤ) : List ℤ := padd p (pscale (-1) q)

lemma pev_psub (p q : List ℤ) (x : ℝ) : pev (psub p q) x = pev p x - pev q x := by
  rw [psub, pev_padd, pev_pscale]
  push_cast
  ring

/-- Power of a dense integer polynomial. -/
@[expose]
def ppow (p : List ℤ) : ℕ → List ℤ
  | 0 => [1]
  | k + 1 => pmul p (ppow p k)

lemma pev_ppow (p : List ℤ) (k : ℕ) (x : ℝ) : pev (ppow p k) x = pev p x ^ k := by
  induction k with
  | zero => simp [ppow]
  | succ k ih => rw [ppow, pev_pmul, ih, pow_succ, mul_comm]

lemma pev_lin (p q : ℤ) (x : ℝ) : pev [p, -q] x = p - q * x := by
  simp [pev]
  ring

lemma pev_three_add (x : ℝ) : pev [3, 1] x = 3 + x := by simp [pev]

lemma pev_X (x : ℝ) : pev [0, 1] x = x := by simp [pev]

/-! ### Bernstein expansion -/

/-- `bern p q d b` is `∑ⱼ bⱼ Xʲ (p - q X)^(d-j)` as a coefficient list, the entries of `b`
being listed from `j = 0`. -/
@[expose]
def bern (p q : ℤ) : ℕ → List ℤ → List ℤ
  | _, [] => []
  | d, a :: rest => padd (pscale a (ppow [p, -q] d)) (0 :: bern p q (d - 1) rest)

lemma pev_bern_cons (p q : ℤ) (d : ℕ) (a : ℤ) (rest : List ℤ) (x : ℝ) :
    pev (bern p q d (a :: rest)) x
      = a * (p - q * x) ^ d + x * pev (bern p q (d - 1) rest) x := by
  rw [bern, pev_padd, pev_pscale, pev_ppow, pev_lin, pev_cons]
  push_cast
  ring

lemma bern_nonneg {p q : ℤ} {x : ℝ} (hx : 0 ≤ x) (hxp : (q : ℝ) * x ≤ p) :
    ∀ (d : ℕ) (b : List ℤ), (∀ a ∈ b, 0 ≤ a) → 0 ≤ pev (bern p q d b) x := by
  intro d b
  induction b generalizing d with
  | nil => intro _; simp [bern]
  | cons a rest ih =>
    intro hb
    rw [pev_bern_cons]
    have ha : (0 : ℝ) ≤ a := by exact_mod_cast hb a (List.mem_cons_self ..)
    have hrest := ih (d - 1) (fun c hc => hb c (List.mem_cons_of_mem a hc))
    have hlin : (0 : ℝ) ≤ p - q * x := by linarith
    exact add_nonneg (mul_nonneg ha (pow_nonneg hlin d)) (mul_nonneg hx hrest)

lemma bern_pos {p q : ℤ} (hp : 0 < p) {x : ℝ} (hx : 0 ≤ x) (hxp : (q : ℝ) * x ≤ p) :
    ∀ (d : ℕ) (b : List ℤ), b.length = d + 1 → (∀ a ∈ b, 0 < a) →
      0 < pev (bern p q d b) x := by
  intro d b
  induction b generalizing d with
  | nil => intro h; simp at h
  | cons a rest ih =>
    intro hlen hb
    have ha : (0 : ℝ) < a := by exact_mod_cast hb a (List.mem_cons_self ..)
    have hlin : (0 : ℝ) ≤ p - q * x := by linarith
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp
    rcases rest with _ | ⟨c, rest⟩
    · obtain rfl : d = 0 := by simpa using hlen
      rw [pev_bern_cons]
      simpa [bern] using ha
    · obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by simp at hlen; omega⟩
      rw [pev_bern_cons, Nat.add_sub_cancel]
      have hrest := ih d' (by simpa using hlen) (fun e he => hb e (List.mem_cons_of_mem a he))
      rcases lt_or_eq_of_le hxp with hlt | heq
      · have h1 : (0 : ℝ) < a * (p - q * x) ^ (d' + 1) :=
          mul_pos ha (pow_pos (by linarith) _)
        have h2 : (0 : ℝ) ≤ x * pev (bern p q d' (c :: rest)) x := mul_nonneg hx hrest.le
        linarith
      · have hxpos : 0 < x := by
          rcases hx.lt_or_eq with h | h
          · exact h
          · rw [← h, mul_zero] at heq
            linarith
        have h1 : (0 : ℝ) ≤ a * (p - q * x) ^ (d' + 1) :=
          mul_nonneg ha.le (pow_nonneg hlin _)
        have h2 : (0 : ℝ) < x * pev (bern p q d' (c :: rest)) x := mul_pos hxpos hrest
        linarith

/-- Positivity from a Bernstein certificate: if `bern p q d B = pscale (p ^ d) P` and every
entry of `B` is positive, then `P` is positive on `[0, p/q]`.  All closed hypotheses are
decidable and are discharged by the kernel in the batch files. -/
theorem pev_pos_of_bern (P B : List ℤ) (p q : ℤ) (d : ℕ) (hp : 0 < p) (_hq : 0 < q)
    (hlen : B.length = d + 1) (hpos : ∀ a ∈ B, 0 < a)
    (hcert : bern p q d B = pscale (p ^ d) P)
    {x : ℝ} (hx : 0 ≤ x) (hxp : (q : ℝ) * x ≤ p) : 0 < pev P x := by
  have h := bern_pos hp hx hxp d B hlen hpos
  rw [hcert, pev_pscale] at h
  have hpd : (0 : ℝ) < ((p ^ d : ℤ) : ℝ) := by exact_mod_cast pow_pos hp d
  rcases lt_or_ge 0 (pev P x) with hpos | hneg
  · exact hpos
  · exfalso
    have := mul_nonpos_of_nonneg_of_nonpos hpd.le hneg
    linarith

/-! ### The batch bound as a rational function -/

/-- The denominator of the batch bound of `Sendov.R_le_batch`, after the moment
substitution, as a polynomial in `α`: with `m₀ = n₀ - 1` and `m₁ = n₁ - 1`,
`12 m₀ m₁² L (2m₀)^k (3+α)^(k+1)`. -/
@[expose]
def batchD (n₀ n₁ k : ℕ) (L : ℤ) : List ℤ :=
  pscale (12 * ((n₀ : ℤ) - 1) * ((n₁ : ℤ) - 1) ^ 2 * L * (2 * ((n₀ : ℤ) - 1)) ^ k)
    (ppow [3, 1] (k + 1))

/-- The numerator of the batch bound over the denominator `Sendov.batchD`. -/
@[expose]
def batchN (n₀ n₁ k : ℕ) (L : ℤ) (Nmom : List ℤ) : List ℤ :=
  padd (pscale (2 * ((n₀ : ℤ) - 1) * ((n₁ : ℤ) - 1) ^ 2 * (L * (2 * ((n₀ : ℤ) - 1)) ^ k))
      (ppow [3, 1] (k + 1)))
    (padd (pscale (3 * ((n₀ : ℤ) - 1) * ((n₁ : ℤ) - 1) ^ 2 * (L * (2 * ((n₀ : ℤ) - 1)) ^ k))
        (ppow [3, 1] k))
      (padd (pscale (6 * ((n₁ : ℤ) - 1) ^ 2 * (L * (2 * ((n₀ : ℤ) - 1)) ^ k))
          (ppow [3, 1] (k + 1)))
        (padd (pscale (3 * ((n₁ : ℤ) - 1) ^ 2 * (L * (2 * ((n₀ : ℤ) - 1)) ^ k))
            (ppow [3, 1] k))
          (pscale (3 * ((n₀ : ℤ) - 1) * n₁ * ((n₁ : ℤ) - 1) * ((n₁ : ℤ) - 2))
            (pmul (ppow [((n₁ : ℤ) - 1), -2] 2) Nmom)))))

/-- The numerator of `1 - bound`: the polynomial that each batch certifies positive. -/
@[expose]
def batchP (n₀ n₁ k : ℕ) (L : ℤ) (Nmom : List ℤ) : List ℤ :=
  psub (batchD n₀ n₁ k L) (batchN n₀ n₁ k L Nmom)

lemma two_alpha_le_of_le {n n₁ : ℕ} {α : ℝ} (hn : 2 ≤ n) (h1 : n ≤ n₁)
    (hfeas : c n α ^ 2 ≤ A n α) : 2 * α ≤ (n₁ : ℝ) - 1 := by
  have h := alpha_le_half_M hn hfeas
  have hcast : (n : ℝ) ≤ n₁ := by exact_mod_cast h1
  simp only [M] at h
  linarith

/-- **The batch bound is below `1`** once its numerator `Sendov.batchP` is positive.  The
hypothesis `hint` is the packed moment identity of the batch (`Sendov.integral_moment_packed`),
and the conclusion is exactly the right-hand side of `Sendov.R_le_batch`. -/
theorem batch_lt_one {n₀ n₁ k : ℕ} (hn₀ : 5 ≤ n₀) (hk : n₀ = 2 * k + 4) (h01 : n₀ ≤ n₁)
    (L : ℤ) (hL : 0 < L) (Nmom : List ℤ) {α : ℝ} (hα : 0 ≤ α)
    (hint : (∫ t in (0 : ℝ)..1, t ^ 3 * Q n₀ α t ^ k)
      = pev Nmom α / ((L : ℝ) * (2 * M n₀ * (3 + α)) ^ k))
    (hP : 0 < pev (batchP n₀ n₁ k L Nmom) α) :
    1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * M n₀) + 1 / (4 * M n₀ * (3 + α))
      + A n₁ α ^ 2 * n₁ * M n₁ * ((n₁ : ℝ) - 2) / (4 * (3 + α))
        * ∫ t in (0 : ℝ)..1, t ^ 3 * Q n₀ α t ^ (((n₀ : ℝ) - 4) / 2) < 1 := by
  have hexp : ((n₀ : ℝ) - 4) / 2 = ((k : ℕ) : ℝ) := by
    subst hk
    push_cast
    ring
  simp only [hexp, Real.rpow_natCast]
  rw [hint]
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hm₀ : (0 : ℝ) < (n₀ : ℝ) - 1 := by
    have : (5 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
    linarith
  have hm₁ : (0 : ℝ) < (n₁ : ℝ) - 1 := by
    have : (n₀ : ℝ) ≤ n₁ := by exact_mod_cast h01
    linarith
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hD : (0 : ℝ) < pev (batchD n₀ n₁ k L) α := by
    rw [batchD, pev_pscale, pev_ppow, pev_three_add]
    push_cast
    positivity
  have hS : 1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * M n₀) + 1 / (4 * M n₀ * (3 + α))
      + A n₁ α ^ 2 * n₁ * M n₁ * ((n₁ : ℝ) - 2) / (4 * (3 + α))
        * (pev Nmom α / ((L : ℝ) * (2 * M n₀ * (3 + α)) ^ k))
      = pev (batchN n₀ n₁ k L Nmom) α / pev (batchD n₀ n₁ k L) α := by
    rw [eq_div_iff hD.ne']
    simp only [batchN, batchD, pev_padd, pev_pscale, pev_pmul, pev_ppow, pev_three_add,
      pev_lin, A, M]
    push_cast
    simp only [mul_pow]
    field_simp
    ring
  rw [hS, div_lt_one hD]
  have hsub := pev_psub (batchD n₀ n₁ k L) (batchN n₀ n₁ k L Nmom) α
  rw [batchP] at hP
  linarith

end Sendov
