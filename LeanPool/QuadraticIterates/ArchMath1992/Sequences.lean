/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import LeanPool.QuadraticIterates.Mathlib.Algebra.Polynomial.EvenComp
import LeanPool.QuadraticIterates.Mathlib.Algebra.Squares
import LeanPool.QuadraticIterates.Mathlib.Data.Int.DvdSequence
import LeanPool.QuadraticIterates.Mathlib.Data.ZMod
import LeanPool.QuadraticIterates.Mathlib.RingTheory.MoebiusFactor
import LeanPool.QuadraticIterates.Mathlib.RingTheory.UniqueFactorizationDomain

/-!
# The iteration sequence of a polynomial and its Möbius factors

For `g ∈ R[X]` and a sign `ε`, the sequence `γ_1 = ε · g(0)`, `γ_{n+1} = g(γ_n)` and its Möbius
factors `β_n = ∏_{d ∣ n} γ_d^{μ(n/d)}`. The results are stated at the generality each one needs:
over a `CommSemiring` for the recursion, over a `CommRing` for the congruences, over a GCD domain
for strong divisibility (`gammaSeq_associated_gcd`), over a UFD for the valuation shape
(`factorization_gammaSeq_shape`) and the integrality of `β`, and finally over `ℤ` for Lemmas 2.1
and 2.2 of the paper (`not_isSquare_betaSeq` and `not_isSquare_betaSeq_of_pos`).

Part of the formalization of M. Stoll, *Galois groups over ℚ of some iterated polynomials*,
Arch. Math. **59** (1992), 239-244; see `QuadraticIterates.ArchMath1992`.
-/

open Polynomial
open scoped ArithmeticFunction.Moebius

namespace QuadraticIterates

/-! ### The sequences `γ` and `β`, and even polynomials -/


/-- The iteration sequence `γ_n` of `g ∈ R[X]` with sign choice `ε`: `γ_1 = ε · g(0)`, `γ_{n+1} =
g(γ_n)`; the value at index `0` is `0` (chosen so that over `ℤ`, `γ` is a strong divisibility
sequence). -/
def gammaSeq {R : Type*} [CommSemiring R] (g : R[X]) (ε : R) : ℕ → R
  | 0 => 0
  | 1 => ε * g.eval 0
  | n + 2 => g.eval (gammaSeq g ε (n + 1))

/-- The Möbius factors `β_n = ∏_{d ∣ n} γ_d^{μ(n/d)}` of the `γ`-sequence, as elements of the
coefficient ring: the unique preimage of the fraction-field Möbius product under
`R → FractionRing R` (junk when that product is not integral). -/
noncomputable def betaSeq {R : Type*} [CommRing R] [IsDomain R] (g : R[X]) (ε : R) (n : ℕ) : R :=
  moebiusFactorR (gammaSeq g ε) n

lemma betaSeq_eq_moebiusFactorR {R : Type*} [CommRing R] [IsDomain R] (g : R[X]) (ε : R) (n : ℕ) :
    betaSeq g ε n = moebiusFactorR (gammaSeq g ε) n := rfl

/-- `g` is an even polynomial (`g ∈ R[X²]`): `g = Polynomial.expand R 2 h` for some `h`. -/
def EvenPoly {R : Type*} [CommSemiring R] (g : R[X]) : Prop := ∃ h : R[X], g = expand R 2 h

/-- An even polynomial takes equal values at points with equal squares. -/
theorem EvenPoly.eval_congr {R : Type*} [CommSemiring R] {g : R[X]} (hg : EvenPoly g)
    {x y : R} (h : x ^ 2 = y ^ 2) : g.eval x = g.eval y := by
  obtain ⟨h', rfl⟩ := hg
  rw [expand_eval, expand_eval, h]

/-- An even polynomial defines an even evaluation function. -/
theorem EvenPoly.eval_neg {R : Type*} [CommRing R] {g : R[X]} (hg : EvenPoly g) (y : R) :
    g.eval (-y) = g.eval y := hg.eval_congr (neg_sq y)

/-- Being an even polynomial is preserved by ring homomorphisms. -/
theorem EvenPoly.map {R S : Type*} [CommSemiring R] [CommSemiring S] {g : R[X]}
    (hg : EvenPoly g) (φ : R →+* S) : EvenPoly (g.map φ) := by
  obtain ⟨h, rfl⟩ := hg
  exact ⟨h.map φ, by rw [map_expand]⟩

lemma EvenPoly.dvd_eval_sub {R : Type*} [CommRing R] {g : R[X]} (hg : EvenPoly g)
    {N a b : R} (h : N ∣ a ^ 2 - b ^ 2) : N ∣ g.eval a - g.eval b := by
  obtain ⟨h', rfl⟩ := hg
  rw [expand_eval, expand_eval]
  exact h.trans (sub_dvd_eval_sub (a ^ 2) (b ^ 2) h')

/-- An even polynomial is fixed by `X ↦ -X`. -/
lemma EvenPoly.comp_neg_X {R : Type*} [CommRing R] {g : R[X]} (hg : EvenPoly g) :
    g.comp (-X) = g := by
  obtain ⟨h, rfl⟩ := hg
  exact expand_two_comp_neg_X h

/-- Over a domain of characteristic `≠ 2` the converse holds too, so the two notions of evenness
this file uses — membership in `R[X²]` and invariance under `X ↦ -X` — agree. -/
lemma evenPoly_iff_comp_neg_X {R : Type*} [CommRing R] [NoZeroDivisors R] [NeZero (2 : R)]
    {g : R[X]} : EvenPoly g ↔ g.comp (-X) = g :=
  ⟨EvenPoly.comp_neg_X, fun h ↦ ⟨contract 2 g, eq_expand_two_contract_of_comp_neg_X h⟩⟩


/-! ### The `γ`-sequence over a commutative semiring -/

section

variable {R : Type*} [CommSemiring R] (g : R[X])

@[simp] lemma gammaSeq_zero (ε : R) : gammaSeq g ε 0 = 0 := rfl

@[simp] lemma gammaSeq_one (ε : R) : gammaSeq g ε 1 = ε * g.eval 0 := rfl

/-- The recursion `γ_{n+1} = g(γ_n)`, valid for `n ≥ 1`. -/
lemma gammaSeq_succ (ε : R) {n : ℕ} (hn : 1 ≤ n) :
    gammaSeq g ε (n + 1) = g.eval (gammaSeq g ε n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : n ≠ 0)
  rfl

lemma gammaSeq_add (ε : R) {m : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    gammaSeq g ε (m + n) = (fun z ↦ g.eval z)^[n] (gammaSeq g ε m) := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : m ≠ 0)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show m' + 1 + (n + 1) = m' + n + 1 + 1 by ring, gammaSeq_succ g ε (by lia),
      show m' + n + 1 = m' + 1 + n by ring, ih, Function.iterate_succ_apply']

/-- A ring homomorphism intertwines the `γ`-sequences of `g` and its image:
`φ(γ_n(g, ε)) = γ_n(g.map φ, φ ε)`. -/
lemma map_gammaSeq {S : Type*} [CommSemiring S] (φ : R →+* S) (ε : R) (n : ℕ) :
    φ (gammaSeq g ε n) = gammaSeq (g.map φ) (φ ε) n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [zero_add, gammaSeq_one, map_mul]
      rw [eval_map, ← eval₂_at_apply, map_zero]
    · rw [gammaSeq_succ g ε hm, gammaSeq_succ (g.map φ) (φ ε) hm, ← ih, eval_map, eval₂_at_apply]

/-- The recursion `γ_{n+1} = g(γ_n)` for the `ε = 1` sequence, valid at every index (including `0`,
since `γ_0 = 0` and `γ_1 = g(0)`). -/
lemma gammaSeq_one_succ (n : ℕ) : gammaSeq g 1 (n + 1) = g.eval (gammaSeq g 1 n) := by
  cases n with
  | zero => simp
  | succ m => exact gammaSeq_succ g 1 (by lia)

variable {g}

/-- In a ring with `4 = 0`, the `ε = 1` sequence of an even `g` with `g(0) = 1`, `g(1) = 2`
alternates between `1` and `2`, so consecutive terms sum to `3`. (The only property of `ZMod 4`
used in the mod-4 step is `4 = 0`, which gives `g(2) = g(0)` by evenness.) -/
theorem gammaSeq_add_succ_eq_three (hg : EvenPoly g) (h4 : (4 : R) = 0) (h0 : g.eval 0 = 1)
    (h1 : g.eval 1 = 2) :
    ∀ n ≥ 1, gammaSeq g 1 n + gammaSeq g 1 (n + 1) = 3 := by
  have h22 : (2 : R) ^ 2 = (0 : R) ^ 2 := by
    rw [show (2 : R) ^ 2 = 4 by norm_num, h4, zero_pow two_ne_zero]
  have h20 : g.eval 2 = 1 := (hg.eval_congr h22).trans h0
  have hinv : ∀ m ≥ 1, (gammaSeq g 1 m = 1 ∧ gammaSeq g 1 (m + 1) = 2) ∨
      (gammaSeq g 1 m = 2 ∧ gammaSeq g 1 (m + 1) = 1) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact .inl ⟨by simp [h0], by
        rw [gammaSeq_succ g 1 le_rfl, gammaSeq_one, one_mul, h0, h1]⟩
    | succ k hk ih =>
      rcases ih with ⟨-, hb⟩ | ⟨-, hb⟩
      · exact .inr ⟨hb, by rw [gammaSeq_succ g 1 (by lia), hb, h20]⟩
      · exact .inl ⟨hb, by rw [gammaSeq_succ g 1 (by lia), hb, h1]⟩
  intro n hn
  rcases hinv n hn with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb] <;> norm_num

/-- If `ε² = g(0)² = g(1)² = 1` and `g` is even, then `γ_n = g(1)` for all `n ≥ 2`, so
consecutive terms sum to `2·g(1)`. (The only property of `ZMod 8` used in the mod-8 step is
that the relevant residues square to `1`.) -/
theorem gammaSeq_add_succ_eq_two_mul_eval_one (hg : EvenPoly g) {ε : R} (hε : ε ^ 2 = 1)
    (h0 : g.eval 0 ^ 2 = 1) (h1 : g.eval 1 ^ 2 = 1) :
    ∀ n ≥ 2, gammaSeq g ε n + gammaSeq g ε (n + 1) = 2 * g.eval 1 := by
  have hval : ∀ n ≥ 2, gammaSeq g ε n = g.eval 1 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      rw [show (2 : ℕ) = 1 + 1 from rfl, gammaSeq_succ g ε le_rfl]
      exact hg.eval_congr (by rw [gammaSeq_one, mul_pow, hε, one_mul, h0, one_pow])
    | succ k hk ih =>
      rw [gammaSeq_succ g ε (by lia), ih]
      exact hg.eval_congr (by rw [h1, one_pow])
  intro n hn
  rw [hval n hn, hval (n + 1) (by lia), two_mul]

/-- For even `g` and `ε² = 1`, the `ε`-sequence *equals* the `ε = 1` sequence from index `2` on:
the sign is absorbed by the square inside `g`. -/
theorem gammaSeq_eq_gammaSeq_one (hg : EvenPoly g) {ε : R} (hε : ε ^ 2 = 1) {n : ℕ} (hn : 2 ≤ n) :
    gammaSeq g ε n = gammaSeq g 1 n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by lia⟩
  obtain ⟨h', rfl⟩ := hg
  rw [show j + 2 = 1 + (j + 1) by ring, gammaSeq_add _ ε le_rfl (j + 1),
    gammaSeq_add _ 1 le_rfl (j + 1), Function.iterate_succ_apply,
    Function.iterate_succ_apply, gammaSeq_one, gammaSeq_one, one_mul,
    expand_eval, expand_eval, mul_pow, hε, one_mul, expand_eval]

/-- For even `g` and `ε² = 1`, the `ε`-sequence is associated to the `ε = 1` sequence: the two
agree from index `2` on and differ by the unit `ε` at index `1`. -/
theorem gammaSeq_associated_one (hg : EvenPoly g) {ε : R} (hε : ε ^ 2 = 1) (n : ℕ) :
    Associated (gammaSeq g ε n) (gammaSeq g 1 n) := by
  match n with
  | 0 => simp
  | 1 => simpa using associated_unit_mul_left (g.eval 0) ε (IsUnit.of_pow_eq_one hε two_ne_zero)
  | (_ + 2) => rw [gammaSeq_eq_gammaSeq_one hg hε (by lia)]

end

/-! ### The `γ`-sequence over a commutative ring -/

section

variable {R : Type*} [CommRing R] (g : R[X])

/-- The `ε = 1` sequence satisfies the translation congruence `γ_m ∣ γ_{m+j} - γ_j`. -/
private lemma gammaSeq_one_dvd_sub (m j : ℕ) :
    gammaSeq g 1 m ∣ gammaSeq g 1 (m + j) - gammaSeq g 1 j := by
  have step (k l : ℕ) : gammaSeq g 1 k - gammaSeq g 1 l ∣
      gammaSeq g 1 (k + 1) - gammaSeq g 1 (l + 1) := by
    rw [gammaSeq_one_succ, gammaSeq_one_succ]
    exact sub_dvd_eval_sub _ _ g
  induction j with
  | zero => simp
  | succ j ih => exact ih.trans (step (m + j) j)

variable {g}

/-- **Strong divisibility of the `γ`-sequence over a GCD domain**: for even `g` and `ε² = 1`,
`gcd (γ_m) (γ_n)` is associated to `γ_{gcd m n}`. -/
theorem gammaSeq_associated_gcd [IsDomain R] [NormalizedGCDMonoid R] (hg : EvenPoly g) {ε : R}
    (hε : ε ^ 2 = 1) (m n : ℕ) :
    Associated (gcd (gammaSeq g ε m) (gammaSeq g ε n)) (gammaSeq g ε (m.gcd n)) :=
  (((gammaSeq_associated_one hg hε m).gcd (gammaSeq_associated_one hg hε n)).trans
    (associated_gcd_of_dvd_sub rfl (gammaSeq_one_dvd_sub g) m n)).trans
    (gammaSeq_associated_one hg hε (m.gcd n)).symm

variable (g) in
/-- Periodicity propagates along the recursion: a divisor of `γ_{n₀+m} - γ_{n₀}` divides
`γ_{n+m} - γ_n` for all `n ≥ n₀ ≥ 1`. -/
lemma gammaSeq_period {ε : R} {m : ℕ} {n₀ : ℕ} (hn₀ : 1 ≤ n₀) {q : R}
    (hbase : q ∣ gammaSeq g ε (n₀ + m) - gammaSeq g ε n₀) :
    ∀ n ≥ n₀, q ∣ gammaSeq g ε (n + m) - gammaSeq g ε n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hbase
  | succ n hn ih =>
    rw [show n + 1 + m = (n + m) + 1 by ring, gammaSeq_succ g ε (by lia),
      gammaSeq_succ g ε (by lia)]
    exact ih.trans (sub_dvd_eval_sub _ _ g)

/-- For even `g`, `γ_n ^ 2` divides `γ_{n+1} - g(0)` (`n ≥ 1`). -/
lemma sq_dvd_gammaSeq_succ_sub (hg : EvenPoly g) (ε : R) {n : ℕ} (hn : 1 ≤ n) :
    gammaSeq g ε n ^ 2 ∣ gammaSeq g ε (n + 1) - g.eval 0 := by
  rw [gammaSeq_succ g ε hn]
  exact hg.dvd_eval_sub (by simp)

/-- Sharpening of `sq_dvd_gammaSeq_succ_sub`: a prime power `p^E` with `E ≥ 1` dividing `γ_n`
already forces `p^{E+1} ∣ γ_{n+1} - g(0)` (`n ≥ 1`). -/
lemma pow_succ_dvd_gammaSeq_succ_sub (hg : EvenPoly g) {ε : R} {n : ℕ} (hn : 1 ≤ n) {p : R}
    {E : ℕ} (hE : 1 ≤ E) (hpE : p ^ E ∣ gammaSeq g ε n) :
    p ^ (E + 1) ∣ gammaSeq g ε (n + 1) - g.eval 0 :=
  calc p ^ (E + 1) ∣ p ^ (2 * E) := pow_dvd_pow p (by lia)
    _ ∣ gammaSeq g ε n ^ 2 := by rw [two_mul, pow_add, sq]; exact mul_dvd_mul hpE hpE
    _ ∣ gammaSeq g ε (n + 1) - g.eval 0 := sq_dvd_gammaSeq_succ_sub hg ε hn

/-- If `γ_k + γ_{2k} = 0`, then `γ_{lk} = γ_{2k}` for all `l ≥ 2` (over any ring, for even `g`):
`γ` is constant on positive multiples of `k` past the first. -/
theorem gammaSeq_mul_eq_two_mul (hg : EvenPoly g) {ε : R} {k : ℕ} (hk : 1 ≤ k)
    (hzero : gammaSeq g ε k + gammaSeq g ε (2 * k) = 0) :
    ∀ l ≥ 2, gammaSeq g ε (l * k) = gammaSeq g ε (2 * k) := by
  have hγ (i j : ℕ) (hi : 1 ≤ i) :
      gammaSeq g ε (i + j) = (fun z ↦ g.eval z)^[j] (gammaSeq g ε i) := gammaSeq_add g ε hi j
  have hevenk (y : R) : (fun z ↦ g.eval z)^[k] (-y) = (fun z ↦ g.eval z)^[k] y := by
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : k ≠ 0)
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hg.eval_neg]
  have hneg : gammaSeq g ε (2 * k) = -gammaSeq g ε k := by linear_combination hzero
  have hfix : (fun z ↦ g.eval z)^[k] (gammaSeq g ε (2 * k)) = gammaSeq g ε (2 * k) := by
    rw [hneg, hevenk, ← hγ k k hk, ← two_mul, hneg]
  intro l hl
  induction l, hl using Nat.le_induction with
  | base => rfl
  | succ l hl ih =>
    rw [show (l + 1) * k = l * k + k by ring, hγ (l * k) k (one_le_mul (by lia) hk), ih, hfix]

/-- A product of terms each equal to `α · (-1 if t = 1 else 1)` collapses to `α ^ |S|` times a
single sign depending on whether `1 ∈ S`. -/
private theorem prod_eq_pow_card_mul_ite {α : R} {S : Finset ℕ} {f : ℕ → R}
    (hf : ∀ t ∈ S, f t = α * (if t = 1 then (-1 : R) else 1)) :
    (∏ t ∈ S, f t) = α ^ S.card * (if 1 ∈ S then (-1 : R) else 1) := by
  rw [Finset.prod_congr rfl hf, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_ite_eq' S 1 (fun _ ↦ (-1 : R))]

/-- If `γ_k + γ_{2k} = 0`, then a product `∏_{t ∈ S} γ_{kt}` over positive indices `t` collapses
to `γ_{2k} ^ |S|` up to a sign recording whether `1 ∈ S` (over any ring, for even `g`). -/
theorem prod_gammaSeq_mul_eq (hg : EvenPoly g) {ε : R} {k : ℕ} (hk : 1 ≤ k)
    (hzero : gammaSeq g ε k + gammaSeq g ε (2 * k) = 0)
    {S : Finset ℕ} (hS : ∀ t ∈ S, 1 ≤ t) :
    (∏ t ∈ S, gammaSeq g ε (k * t))
      = gammaSeq g ε (2 * k) ^ S.card * (if 1 ∈ S then -1 else 1) := by
  have hγk_neg : gammaSeq g ε k = -gammaSeq g ε (2 * k) := by linear_combination hzero
  refine prod_eq_pow_card_mul_ite fun t ht ↦ ?_
  have ht1 : 1 ≤ t := hS t ht
  rcases eq_or_ne t 1 with rfl | h
  · rw [mul_one, ite_eq_left rfl, mul_neg, mul_one, hγk_neg]
  · rw [ite_eq_right h, mul_one, mul_comm k t, gammaSeq_mul_eq_two_mul hg hk hzero t (by lia)]

/-- If `γ_n + γ_{n+1} = 0`, then `γ_{n+j} = γ_{n+1}` for all `j ≥ 1` (over any ring, for even `g`):
the fixed-point relation `g(γ_{n+1}) = γ_{n+1}` makes `γ` constant past index `n`. -/
theorem gammaSeq_add_eq_succ (hg : EvenPoly g) {ε : R} {n : ℕ} (hn : 1 ≤ n)
    (hzero : gammaSeq g ε n + gammaSeq g ε (n + 1) = 0) :
    ∀ j ≥ 1, gammaSeq g ε (n + j) = gammaSeq g ε (n + 1) := by
  have hsucc (m : ℕ) (hm : 1 ≤ m) : gammaSeq g ε (m + 1) = g.eval (gammaSeq g ε m) :=
    gammaSeq_succ g ε hm
  have hneg : gammaSeq g ε (n + 1) = -gammaSeq g ε n := by linear_combination hzero
  have hstep : g.eval (gammaSeq g ε (n + 1)) = gammaSeq g ε (n + 1) := by
    conv_lhs => rw [hneg, hg.eval_neg, ← hsucc n hn]
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ j hj ih => rw [show n + (j + 1) = (n + j) + 1 by ring, hsucc (n + j) (by lia), ih, hstep]

/-- For even `g`, `γ_n + γ_{n+1}` divides `γ_n + γ_{2n}` (`n ≥ 1`): modulo the left-hand side the
sequence is constant from index `n + 1` on, so `γ_{2n} ≡ γ_{n+1}`. -/
lemma gammaSeq_add_succ_dvd (hg : EvenPoly g) (ε : R) {n : ℕ} (hn : 1 ≤ n) :
    gammaSeq g ε n + gammaSeq g ε (n + 1) ∣ gammaSeq g ε n + gammaSeq g ε (2 * n) := by
  set D := gammaSeq g ε n + gammaSeq g ε (n + 1) with hD
  set π := Ideal.Quotient.mk (Ideal.span {D})
  have hz : gammaSeq (g.map π) (π ε) n + gammaSeq (g.map π) (π ε) (n + 1) = 0 := by
    rw [← map_gammaSeq, ← map_gammaSeq, ← map_add, ← hD, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton]
  have key : π (gammaSeq g ε (n + n)) = π (gammaSeq g ε (n + 1)) := by
    rw [map_gammaSeq, map_gammaSeq]
    exact gammaSeq_add_eq_succ (hg.map _) hn hz n hn
  have hsplit : gammaSeq g ε n + gammaSeq g ε (2 * n)
      = D + (gammaSeq g ε (n + n) - gammaSeq g ε (n + 1)) := by rw [hD, two_mul]; ring
  rw [hsplit]
  exact dvd_add dvd_rfl (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp key))

variable (g) in
/-- `γ_{n+1} ≡ g(0)` modulo `γ_n`, so `γ_n + γ_{n+1}` and `γ_n` are coprime once `g(0)` is a
unit (`n ≥ 1`). -/
lemma isCoprime_gammaSeq_add_succ (ε : R) {n : ℕ} (hn : 1 ≤ n) (h0 : IsUnit (g.eval 0)) :
    IsCoprime (gammaSeq g ε n + gammaSeq g ε (n + 1)) (gammaSeq g ε n) := by
  obtain ⟨k, hk⟩ := sub_dvd_eval_sub (gammaSeq g ε n) 0 g
  have heq : gammaSeq g ε n + gammaSeq g ε (n + 1) = g.eval 0 + gammaSeq g ε n * (1 + k) := by
    rw [gammaSeq_succ g ε hn]; linear_combination hk
  rw [heq]
  exact ((isCoprime_zero_right.mpr h0).of_isCoprime_of_dvd_right (dvd_zero _)).add_mul_left_left _

end

/-! ### Valuations of the `γ`-sequence over a UFD -/

section

variable {R : Type*} [CommRing R] [UniqueFactorizationMonoid R]
    [NormalizationMonoid R] [DecidableEq R] {g : R[X]}

/-- If `p ∣ g(0)`, the valuation `v_p(γ_n)` is the constant `v_p(g(0))`. -/
lemma factorization_gammaSeq_of_dvd_eval_zero (hg : EvenPoly g) {ε : R} (hε : ε ^ 2 = 1)
    (hne : ∀ k ≥ 1, gammaSeq g ε k ≠ 0) {p : R} (hp : Prime p) (hpn : normalize p = p)
    (hpg : p ∣ g.eval 0) {n : ℕ} (hn : 1 ≤ n) :
    factorization (gammaSeq g ε n) p = factorization (g.eval 0) p := by
  have hg0 : g.eval 0 ≠ 0 := fun h ↦ hne 1 le_rfl (by rw [gammaSeq_one, h, mul_zero])
  have hεu : IsUnit ε := IsUnit.of_pow_eq_one hε two_ne_zero
  have hv1 := (one_le_factorization_iff_dvd hp hpn hg0).mpr hpg
  induction n, hn using Nat.le_induction with
  | base =>
    have hassoc : Associated (gammaSeq g ε 1) (g.eval 0) := by
      rw [gammaSeq_one]
      exact associated_unit_mul_left (g.eval 0) ε hεu
    rw [factorization_eq_count, hassoc.normalizedFactors_eq, ← factorization_eq_count]
  | succ k hk ih =>
    refine factorization_eq_of_dvd_sub hp hpn (hne (k + 1) (by lia)) hg0 rfl ?_
    exact pow_succ_dvd_gammaSeq_succ_sub hg hk hv1
      ((pow_dvd_iff_le_factorization hp hpn (hne k hk)).mpr ih.ge)

/-- The main case: if `p ∤ g(0)` but `p` divides some `γ_m`, the valuation `v_p(γ_n)` is
supported on the multiples of the minimal such index `m`, with constant value. -/
private lemma factorization_gammaSeq_shape_of_exists (hg : EvenPoly g) {ε : R} (hε : ε ^ 2 = 1)
    (hne : ∀ k ≥ 1, gammaSeq g ε k ≠ 0) {p : R} (hp : Prime p) (hpn : normalize p = p)
    (hpg : ¬p ∣ g.eval 0) (hex : ∃ k : ℕ, 1 ≤ k ∧ p ∣ gammaSeq g ε k) :
    ∃ m ≥ 1, ∃ E : ℕ, ∀ n ≥ 1,
      factorization (gammaSeq g ε n) p = if m ∣ n then E else 0 := by
  classical
  have hεu : IsUnit ε := IsUnit.of_pow_eq_one hε two_ne_zero
  obtain ⟨m, hm1, hpm, hmin⟩ :
      ∃ m : ℕ, 1 ≤ m ∧ p ∣ gammaSeq g ε m ∧
        ∀ k < m, ¬ (1 ≤ k ∧ p ∣ gammaSeq g ε k) :=
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun _ ↦ Nat.find_min hex⟩
  have hm1' : m ≠ 1 := by
    rintro rfl
    rw [gammaSeq_one] at hpm
    exact hpg ((hp.dvd_mul.mp hpm).resolve_left fun h ↦ hp.not_isUnit (isUnit_of_dvd_unit h hεu))
  have hm2 : 2 ≤ m := by lia
  set E := factorization (gammaSeq g ε m) p with hE
  have hE1 := (one_le_factorization_iff_dvd hp hpn (hne m hm1)).mpr hpm
  have hpEm : p ^ E ∣ gammaSeq g ε m := (pow_dvd_iff_le_factorization hp hpn (hne m hm1)).mpr le_rfl
  -- `p^{E+1} ∣ γ_{m+1} - g(0)` via `γ_m² ∣ γ_{m+1} - g(0)`
  have hcm1 := pow_succ_dvd_gammaSeq_succ_sub hg hm1 hE1 hpEm
  have hpncm1 : ¬ p ∣ gammaSeq g ε (m + 1) := by
    intro hdvd
    refine hpg ?_
    rw [← sub_sub_self (gammaSeq g ε (m + 1)) (g.eval 0)]
    exact dvd_sub hdvd ((dvd_pow_self p (by lia : E + 1 ≠ 0)).trans hcm1)
  -- base of the periodicity: `p^{E+1} ∣ γ_{2+m} - γ_2`
  have hbase : p ^ (E + 1) ∣ gammaSeq g ε (2 + m) - gammaSeq g ε 2 := by
    rw [show 2 + m = (m + 1) + 1 by ring, gammaSeq_succ g ε (by lia),
      show (2 : ℕ) = 1 + 1 from rfl, gammaSeq_succ g ε le_rfl]
    refine hg.dvd_eval_sub ?_
    have hsq : gammaSeq g ε (m + 1) ^ 2 - gammaSeq g ε 1 ^ 2
        = (gammaSeq g ε (m + 1) - g.eval 0) * (gammaSeq g ε (m + 1) + g.eval 0) := by
      rw [gammaSeq_one]
      linear_combination (-(g.eval 0) ^ 2) * hε
    rw [hsq]
    exact hcm1.mul_right _
  exact ⟨m, hm1, E, factorization_periodic_shape hp hpn (gammaSeq g ε) m E hm2 hne hE.symm
    hmin hpncm1 (gammaSeq_period g (by lia) hbase)⟩

/-- **Constant-valuation shape of the `γ`-sequence over a UFD** (for even `g`, `ε² = 1`, `γ`
nowhere zero): for each normalized prime `p`, the valuation `v_p(γ_n)` equals a constant `E`
on the multiples of some index `m ≥ 1` and vanishes elsewhere. -/
theorem factorization_gammaSeq_shape (hg : EvenPoly g) {ε : R} (hε : ε ^ 2 = 1)
    (hne : ∀ k ≥ 1, gammaSeq g ε k ≠ 0) {p : R} (hp : Prime p) (hpn : normalize p = p) :
    ∃ m ≥ 1, ∃ E : ℕ, ∀ n ≥ 1,
      factorization (gammaSeq g ε n) p = if m ∣ n then E else 0 := by
  by_cases hpg : p ∣ g.eval 0
  · exact ⟨1, le_rfl, factorization (g.eval 0) p, fun n hn ↦ by
      rw [ite_eq_left (one_dvd n)]
      exact factorization_gammaSeq_of_dvd_eval_zero hg hε hne hp hpn hpg hn⟩
  · by_cases hex : ∃ k : ℕ, 1 ≤ k ∧ p ∣ gammaSeq g ε k
    · exact factorization_gammaSeq_shape_of_exists hg hε hne hp hpn hpg hex
    · exact ⟨1, le_rfl, 0, fun n hn ↦ by
        rw [ite_eq_left (one_dvd n), factorization_eq_zero_iff_not_dvd hp hpn (hne n hn)]
        exact fun hd ↦ hex ⟨n, hn, hd⟩⟩

end

/-! ### The `γ`- and `β`-sequences over `ℤ` -/

section

variable (g : ℤ[X])

/-- The Möbius factor `∏_{d ∣ n} c_d^{μ(n/d)}` of an integer sequence `c`, as a product over the
divisor antidiagonal of `n`: pairs `(e, d)` with `e * d = n` contribute `c_d ^ μ(e)`. Rational, as
`μ` can be negative; it is an integer when `c` is a strong divisibility sequence. -/
noncomputable def moebiusFactor (c : ℕ → ℤ) (n : ℕ) : ℚ :=
  ∏ x ∈ n.divisorsAntidiagonal, (c x.2 : ℚ) ^ (μ x.1)

lemma moebiusFactor_eq_prod (c : ℕ → ℤ) (n : ℕ) :
    moebiusFactor c n = ∏ x ∈ n.divisorsAntidiagonal, (c x.2 : ℚ) ^ (μ x.1) := rfl

/-- Strong divisibility over `ℤ`, translated from the `Int.gcd`/`natAbs` form into the
`Associated`-of-`GCDMonoid.gcd` form consumed by the `moebiusFactorR` API. -/
lemma associated_gcd_of_int_gcd_eq_natAbs {c : ℕ → ℤ}
    (hsd : ∀ m n, Int.gcd (c m) (c n) = (c (m.gcd n)).natAbs) (m n : ℕ) :
    Associated (gcd (c m) (c n)) (c (m.gcd n)) := by
  rw [Int.associated_iff_natAbs, ← Int.coe_gcd, Int.natAbs_natCast, hsd]

/-- Over `ℤ`, the image in `ℚ` of the integer-valued Möbius factor `moebiusFactorR` is the
`ℚ`-valued Möbius product `moebiusFactor`, for a strong divisibility sequence. -/
lemma intCast_moebiusFactorR {c : ℕ → ℤ} (hc : ∀ d ≥ 1, c d ≠ 0)
    (hsd : ∀ m n, Int.gcd (c m) (c n) = (c (m.gcd n)).natAbs) {n : ℕ} (hn : 1 ≤ n) :
    ((moebiusFactorR c n : ℤ) : ℚ) = moebiusFactor c n := by
  rw [← eq_intCast (algebraMap ℤ ℚ) (moebiusFactorR c n),
    algebraMap_moebiusFactorR hc (associated_gcd_of_int_gcd_eq_natAbs hsd) n hn,
    moebiusFactorK, moebiusFactor_eq_prod]
  exact Finset.prod_congr rfl fun x _ ↦ by norm_num

/-- The image in a ring `S` of the `ε`-sequence over `ℤ` is the `ε`-sequence of the image of `g`:
`(γ_n : S) = γ_n(g.map (· : ℤ → S), ε)`. -/
lemma intCast_gammaSeq (ε : ℤ) (S : Type*) [CommRing S] (i : ℕ) : ((gammaSeq g ε i : ℤ) : S)
    = gammaSeq (g.map (Int.castRingHom S)) (ε : S) i :=
  map_gammaSeq g (Int.castRingHom S) ε i

variable {g}

/-- **Strong divisibility** over `ℤ`, for even `g` and `ε = ±1`:
`gcd (γ_m) (γ_n) = |γ_{gcd m n}|`. -/
theorem gammaSeq_gcd (hg : EvenPoly g) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (m n : ℕ) :
    Int.gcd (gammaSeq g ε m) (gammaSeq g ε n) = (gammaSeq g ε (m.gcd n)).natAbs := by
  have hε2 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have h := Int.associated_iff_natAbs.mp (gammaSeq_associated_gcd hg hε2 m n)
  rw [← h, ← Int.coe_gcd, Int.natAbs_natCast]

/-- The image of `β_n` in `ℚ` is the Möbius product `∏_{ed = n} γ_d^{μ(e)}` (for even `g`,
`ε = ±1`, and `γ` nowhere zero on positive indices). -/
lemma intCast_betaSeq (hg : EvenPoly g) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hγ : ∀ k ≥ 1, gammaSeq g ε k ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    ((betaSeq g ε n : ℤ) : ℚ) = moebiusFactor (gammaSeq g ε) n :=
  intCast_moebiusFactorR hγ (gammaSeq_gcd hg hε) hn

/-- The `ZMod m` specialization of `prod_gammaSeq_mul_eq` via `intCast_gammaSeq`. -/
private lemma prod_gammaSeq_mul_cast_eq (hg : EvenPoly g) {ε : ℤ} {k : ℕ} (hk : 1 ≤ k) {m : ℕ}
    (hdvd : (m : ℤ) ∣ gammaSeq g ε k + gammaSeq g ε (2 * k))
    {S : Finset ℕ} (hS : ∀ t ∈ S, 1 ≤ t) :
    ((∏ t ∈ S, gammaSeq g ε (k * t) : ℤ) : ZMod m)
      = ((gammaSeq g ε (2 * k) : ℤ) : ZMod m) ^ S.card * (if 1 ∈ S then -1 else 1) := by
  have hz : gammaSeq (g.map (Int.castRingHom (ZMod m))) (ε : ZMod m) k
      + gammaSeq (g.map (Int.castRingHom (ZMod m))) (ε : ZMod m) (2 * k) = 0 := by
    rw [← intCast_gammaSeq, ← intCast_gammaSeq, ← Int.cast_add,
      ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hdvd
  rw [Int.cast_prod, intCast_gammaSeq,
    Finset.prod_congr rfl fun t _ ↦ intCast_gammaSeq g ε (ZMod m) (k * t),
    prod_gammaSeq_mul_eq (hg.map _) hk hz hS]

/-- Lemma 2.1: if for each `n ≥ 1` some `m` divides `γ_n + γ_{2n}`, is prime to `γ_n`, and `-1` is
not a square mod `m`, then `β_n` is not a square in `ℚ` for `n ≥ 2`. -/
theorem not_isSquare_betaSeq (hg : EvenPoly g) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hγ : ∀ n ≥ 1, gammaSeq g ε n ≠ 0)
    (hm : ∀ n ≥ 1, ∃ m : ℕ,
      (m : ℤ) ∣ gammaSeq g ε n + gammaSeq g ε (2 * n) ∧
      IsCoprime (m : ℤ) (gammaSeq g ε n) ∧
      ¬IsSquare (-1 : ZMod m)) :
    ∀ n ≥ 2, ¬IsSquare ((betaSeq g ε n : ℤ) : ℚ) := by
  intro n hn2
  set n' := UniqueFactorizationMonoid.radical n
  obtain ⟨k, hk⟩ : n' ∣ n := UniqueFactorizationMonoid.radical_dvd_self
  rw [mul_comm] at hk
  have hn'1 : 1 < n' := Nat.one_lt_radical_iff.mpr (by lia)
  have hkpos : 1 ≤ k := by grind
  obtain ⟨m, hmdvd, hmcop, hmnsq⟩ := hm k hkpos
  obtain ⟨Sp, Sm, hdisj, hunion, hcard, hSp, hSm⟩ :=
    moebius_sign_partition n' hn'1 UniqueFactorizationMonoid.squarefree_radical
  set P : ℤ := ∏ t ∈ Sp, gammaSeq g ε (k * t) with hP
  set Q : ℤ := ∏ t ∈ Sm, gammaSeq g ε (k * t) with hQ
  have hβ : ((betaSeq g ε n : ℤ) : ℚ) = (P : ℚ) / (Q : ℚ) := by
    rw [intCast_betaSeq hg hε hγ n (by lia), moebiusFactor_eq_prod,
      prod_pow_moebius_eq_div n k n' (by lia) rfl hk
        (fun d ↦ ((gammaSeq g ε d : ℤ) : ℚ)) hdisj hunion hSp hSm,
      hP, hQ]
    push_cast
    ring
  set α : ZMod m := ((gammaSeq g ε (2 * k) : ℤ) : ZMod m)
  have hPmod : (P : ZMod m) = α ^ Sp.card * (if 1 ∈ Sp then -1 else 1) :=
    prod_gammaSeq_mul_cast_eq hg hkpos hmdvd fun t ht ↦ Nat.pos_of_mem_divisors
      (hunion ▸ Finset.mem_union_left Sm ht : t ∈ n'.divisors)
  have hQmod : (Q : ZMod m) = α ^ Sm.card * (if 1 ∈ Sm then -1 else 1) :=
    prod_gammaSeq_mul_cast_eq hg hkpos hmdvd fun t ht ↦ Nat.pos_of_mem_divisors
      (hunion ▸ Finset.mem_union_right Sp ht : t ∈ n'.divisors)
  have hone : (1 ∈ Sp ∧ 1 ∉ Sm) ∨ (1 ∉ Sp ∧ 1 ∈ Sm) :=
    (Finset.mem_union.mp (hunion ▸ Nat.one_mem_divisors.mpr (by lia) : (1 : ℕ) ∈ Sp ∪ Sm)).imp
      (fun h ↦ ⟨h, Finset.disjoint_left.mp hdisj h⟩)
      (fun h ↦ ⟨fun h' ↦ Finset.disjoint_left.mp hdisj h' h, h⟩)
  have hα_unit : IsUnit α := ZMod.isUnit_intCast_of_isCoprime_of_dvd_add hmcop hmdvd
  have hQne : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun t ht ↦
    hγ (k * t) (one_le_mul hkpos
      (Nat.pos_of_mem_divisors (hunion ▸ Finset.mem_union_right _ ht)))
  have hPnegQ : (P : ZMod m) = -(Q : ZMod m) := by
    rw [hPmod, hQmod, hcard]
    rcases hone with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  have hQunit : IsUnit (Q : ZMod m) := by
    rw [hQmod]
    exact (hα_unit.pow _).mul (by split_ifs; exacts [isUnit_one.neg, isUnit_one])
  rw [hβ]
  exact fun hsq ↦ hmnsq (ZMod.isSquare_neg_one_of_isSquare_div hQne hPnegQ hQunit hsq)

/-- The `ZMod 4` specialization of `gammaSeq_add_succ_eq_three` via `intCast_gammaSeq`. -/
lemma gammaSeq_add_succ_zmod_four_eq_three (hg : EvenPoly g) (h0 : g.eval 0 = 1)
    (h1 : ((g.eval 1 : ℤ) : ZMod 4) = 2) :
    ∀ n ≥ 1, ((gammaSeq g 1 n + gammaSeq g 1 (n + 1) : ℤ) : ZMod 4) = 3 := by
  intro n hn
  push_cast
  rw [intCast_gammaSeq g 1 (ZMod 4) n, intCast_gammaSeq g 1 (ZMod 4) (n + 1), Int.cast_one]
  exact gammaSeq_add_succ_eq_three (hg.map _) (by decide)
    (by rw [eval_zero_map, h0, map_one])
    (by rw [eval_one_map]; exact_mod_cast h1) n hn

/-- The `ZMod 8` specialization of `gammaSeq_add_succ_eq_two_mul_eval_one` via
`intCast_gammaSeq`; the mod-4 hypothesis on `g(1)` transfers through the canonical map
`ZMod 8 → ZMod 4`. -/
lemma gammaSeq_add_succ_zmod_eight_eq_six (hg : EvenPoly g) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (h0 : g.eval 0 = 1 ∨ g.eval 0 = -1) (h1 : ((g.eval 1 : ℤ) : ZMod 4) = 3) :
    ∀ n ≥ 2, ((gammaSeq g ε n + gammaSeq g ε (n + 1) : ℤ) : ZMod 8) = 6 := by
  have hfiber : ∀ x : ZMod 8, ZMod.castHom (by norm_num : (4 : ℕ) ∣ 8) (ZMod 4) x = 3 →
      x ^ 2 = 1 ∧ 2 * x = 6 := by decide
  obtain ⟨hsq1, h2x⟩ := hfiber ((g.eval 1 : ℤ) : ZMod 8) (by rw [map_intCast]; exact h1)
  intro n hn
  push_cast
  rw [intCast_gammaSeq g ε (ZMod 8) n, intCast_gammaSeq g ε (ZMod 8) (n + 1),
    gammaSeq_add_succ_eq_two_mul_eval_one (hg.map _)
      (by rcases hε with rfl | rfl <;> decide)
      (by rw [eval_zero_map]; rcases h0 with h0' | h0' <;> rw [h0'] <;> decide)
      (by rw [eval_one_map, eq_intCast]; exact hsq1) n hn,
    eval_one_map, eq_intCast]
  exact h2x

/-- Lemma 2.2: if all `γ_n > 0` and either `g(0) = 1, g(1) ≡ 2 mod 4`, or `g(0) = ±1, g(1) ≡ 3 mod
4`, then `β_n` is not a square in `ℚ` for `n ≥ 2`. -/
theorem not_isSquare_betaSeq_of_pos (hg : EvenPoly g) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hpos : ∀ n ≥ 1, 0 < gammaSeq g ε n)
    (hcase : (g.eval 0 = 1 ∧ g.eval 1 % 4 = 2) ∨
      ((g.eval 0 = 1 ∨ g.eval 0 = -1) ∧ g.eval 1 % 4 = 3)) :
    ∀ n ≥ 2, ¬IsSquare ((betaSeq g ε n : ℤ) : ℚ) := by
  have heval0 : g.eval 0 = 1 ∨ g.eval 0 = -1 := by
    rcases hcase with ⟨h0, -⟩ | ⟨h0, -⟩
    exacts [.inl h0, h0]
  refine not_isSquare_betaSeq hg hε (fun n hn ↦ (hpos n hn).ne') fun n hn ↦ ?_
  set D : ℤ := gammaSeq g ε n + gammaSeq g ε (n + 1) with hD
  have hDpos : 0 < D := add_pos (hpos n hn) (hpos (n + 1) (by lia))
  have hdtn : (D.toNat : ℤ) = D := Int.toNat_of_nonneg hDpos.le
  refine ⟨D.toNat, by rw [hdtn]; exact gammaSeq_add_succ_dvd hg ε hn,
    by rw [hdtn]; exact isCoprime_gammaSeq_add_succ g ε hn (Int.isUnit_iff.mpr heval0), ?_⟩
  rcases hcase with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · obtain rfl : ε = 1 := by
      have hp1 := hpos 1 le_rfl
      rw [gammaSeq_one, h0, mul_one] at hp1
      rcases hε with rfl | rfl
      · rfl
      · exact absurd hp1 (by decide)
    refine ZMod.not_isSquare_neg_one_of_dvd dvd_rfl ?_
    have h1' : ((g.eval 1 : ℤ) : ZMod 4) = 2 :=
      (ZMod.intCast_eq_intCast_iff' (g.eval 1) 2 4).mpr (by lia)
    have hsum : (D : ZMod 4) = 3 := gammaSeq_add_succ_zmod_four_eq_three hg h0 h1' n hn
    have := ((ZMod.intCast_eq_intCast_iff D 3 4).mp (mod_cast hsum)).dvd
    lia
  · rcases Nat.lt_or_ge n 2 with hn1 | hn2
    · obtain rfl : n = 1 := by lia
      have hγ1 : gammaSeq g ε 1 = 1 := by
        have hp1 := hpos 1 le_rfl
        rw [gammaSeq_one] at hp1 ⊢
        rcases hε with rfl | rfl <;> rcases h0 with h0' | h0' <;> rw [h0'] at hp1 ⊢ <;> lia
      have hγ2 : gammaSeq g ε 2 = g.eval 1 := by
        rw [gammaSeq_succ g ε le_rfl, hγ1]
      exact ZMod.not_isSquare_neg_one_of_four_dvd
        (mod_cast (by rw [hdtn, hD, hγ1, hγ2]; lia : (4 : ℤ) ∣ (D.toNat : ℤ)))
    · have h1' : ((g.eval 1 : ℤ) : ZMod 4) = 3 :=
        (ZMod.intCast_eq_intCast_iff' (g.eval 1) 3 4).mpr (by lia)
      have hmod8 : D % 8 = 6 := by
        have hcast := gammaSeq_add_succ_zmod_eight_eq_six hg hε heval0 h1' n hn2
        have := ((ZMod.intCast_eq_intCast_iff D 6 8).mp (mod_cast hcast)).dvd
        omega
      exact ZMod.not_isSquare_neg_one_of_dvd
        (Nat.div_dvd_of_dvd (show 2 ∣ D.toNat by lia)) (by lia)

end

end QuadraticIterates
