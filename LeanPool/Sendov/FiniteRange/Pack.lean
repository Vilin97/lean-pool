/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Kronecker packing of dense polynomials

`Sendov.qrow` computes the coefficients of `(g₀ + g₁t + g₂t²) ^ k` as a `List (List ℤ)`.
That is correct but the kernel evaluates list recursion by interpretation, which costs
`Θ(k³)` interpreted steps: measured, `k = 24` takes two minutes and `k = 32` over twenty.

Kernel `Nat` arithmetic, by contrast, is GMP-backed and fast — a 4000-digit multiplication
and a 50th power are milliseconds.  So the fix is to change the *representation*, not the
algorithm: pack a dense polynomial into a single natural number by evaluating it at a base
`b = 2 ^ B` larger than every coefficient.  Multiplication of polynomials then becomes
multiplication of naturals, and the whole recurrence collapses to `base ^ k`, one
exponentiation.  Measured on the real shapes, `k = 46` drops from hours to about half a
second.

This file provides the arithmetic core: evaluation `Sendov.npev`, the digit extraction
`Sendov.unpackN`, and the round trip `Sendov.unpackN_npev` saying that packing is faithful
exactly when every coefficient is below the base.  The bound hypothesis is what the caller
must supply, and it is the only genuinely new obligation the packing introduces.

Everything here is about `ℕ`; signed coefficients are handled downstream by splitting a
`ℤ`-polynomial into its positive and negative parts.

## Main statements

* `Sendov.npev_cons`, `Sendov.npev_append`: how evaluation behaves;
* `Sendov.unpackN_npev`: `unpackN b p.length (npev p b) = p` for coefficients below `b`.
-/

public section

namespace Sendov

/-- Evaluate a dense `ℕ`-polynomial (lowest degree first) at `b`, by Horner's rule.  This is
the packing map: `npev p b` is the single natural number representing `p`. -/
@[expose]
def npev : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: p, b => a + b * npev p b

@[simp] lemma npev_nil (b : ℕ) : npev [] b = 0 := rfl

@[simp] lemma npev_cons (a : ℕ) (p : List ℕ) (b : ℕ) :
    npev (a :: p) b = a + b * npev p b := rfl

/-- Recover the first `m` coefficients of a packed polynomial. -/
@[expose]
def unpackN (b : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | m + 1, x => (x % b) :: unpackN b m (x / b)

@[simp] lemma unpackN_zero (b x : ℕ) : unpackN b 0 x = [] := rfl

@[simp] lemma unpackN_succ (b m x : ℕ) :
    unpackN b (m + 1) x = (x % b) :: unpackN b m (x / b) := rfl

/-- **Packing is faithful.**  If every coefficient is smaller than the base, evaluation at
the base loses nothing: the coefficients can be read back off by division with remainder.

This is the standard Kronecker-substitution correctness statement, and the hypothesis
`∀ a ∈ p, a < b` is exactly the overflow condition the caller must discharge. -/
theorem unpackN_npev (b : ℕ) (hb : 0 < b) :
    ∀ p : List ℕ, (∀ a ∈ p, a < b) → unpackN b p.length (npev p b) = p := by
  intro p
  induction p with
  | nil => intro _; rfl
  | cons a p ih =>
    intro hlt
    have ha : a < b := hlt a (List.mem_cons_self ..)
    have hp : ∀ x ∈ p, x < b := fun x hx => hlt x (List.mem_cons_of_mem _ hx)
    have hmod : (a + b * npev p b) % b = a := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
    have hdiv : (a + b * npev p b) / b = npev p b := by
      rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt ha, Nat.zero_add]
    simp only [List.length_cons, npev_cons, unpackN_succ, hmod, hdiv, ih hp]

/-- Evaluation of a concatenation: the second block is shifted by `b ^ (length of the
first)`.  This is what makes the two-dimensional packing work. -/
lemma npev_append (p q : List ℕ) (b : ℕ) :
    npev (p ++ q) b = npev p b + b ^ p.length * npev q b := by
  induction p with
  | nil => simp
  | cons a p ih =>
    simp only [List.cons_append, npev_cons, ih, List.length_cons]
    ring

/-! ### Packing is a ring homomorphism -/

/-- Addition of dense `ℕ`-polynomials. -/
def paddN : List ℕ → List ℕ → List ℕ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, c :: q => (a + c) :: paddN p q

/-- Multiplication of dense `ℕ`-polynomials. -/
def pmulN : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | a :: p, q => paddN (q.map (fun c => a * c)) (0 :: pmulN p q)

/-- The `k`-th power of a dense `ℕ`-polynomial. -/
def ppowN (p : List ℕ) : ℕ → List ℕ
  | 0 => [1]
  | k + 1 => pmulN p (ppowN p k)

lemma npev_paddN (p q : List ℕ) (b : ℕ) :
    npev (paddN p q) b = npev p b + npev q b := by
  induction p generalizing q with
  | nil => simp [paddN]
  | cons a p ih =>
    cases q with
    | nil => simp [paddN]
    | cons c q =>
      simp only [paddN, npev_cons, ih]
      ring

lemma npev_map_mul (a : ℕ) (q : List ℕ) (b : ℕ) :
    npev (q.map (fun c => a * c)) b = a * npev q b := by
  induction q with
  | nil => simp
  | cons c q ih =>
    simp only [List.map_cons, npev_cons, ih]
    ring

lemma npev_pmulN (p q : List ℕ) (b : ℕ) :
    npev (pmulN p q) b = npev p b * npev q b := by
  induction p with
  | nil => simp [pmulN]
  | cons a p ih =>
    simp only [pmulN, npev_paddN, npev_map_mul, npev_cons, ih]
    ring

lemma npev_ppowN (p : List ℕ) (b k : ℕ) : npev (ppowN p k) b = npev p b ^ k := by
  induction k with
  | zero => simp [ppowN]
  | succ k ih => simp only [ppowN, npev_pmulN, ih, pow_succ]; ring

/-! ### The overflow bound -/

/-- Every coefficient is at most the sum of the coefficients, which is the value at `1`. -/
lemma mem_le_npev_one : ∀ (q : List ℕ) (a : ℕ), a ∈ q → a ≤ npev q 1 := by
  intro q
  induction q with
  | nil => intro a ha; cases ha
  | cons c q ih =>
    intro a ha
    rcases List.mem_cons.1 ha with h | h
    · subst h; simp
    · have := ih a h
      simp only [npev_cons, one_mul]
      omega

/-- **Kronecker substitution.**  The coefficients of `p ^ k` are recovered from the single
natural number `(npev p b) ^ k`, provided the base `b` exceeds every coefficient of `p ^ k`
— for which `(npev p 1) ^ k < b` suffices, `npev p 1` being the sum of the coefficients.

This is the statement that lets the kernel replace `Θ(k³)` interpreted list steps by one
GMP-backed exponentiation. -/
theorem unpackN_pow (b : ℕ) (hb : 0 < b) (p : List ℕ) (k : ℕ)
    (hbound : npev p 1 ^ k < b) :
    unpackN b (ppowN p k).length (npev p b ^ k) = ppowN p k := by
  rw [← npev_ppowN p b k]
  refine unpackN_npev b hb _ fun a ha => ?_
  have h1 : a ≤ npev (ppowN p k) 1 := mem_le_npev_one _ a ha
  rw [npev_ppowN] at h1
  omega

/-! ### Signed coefficients

The recurrence's middle coefficient `g₁ = -2Dc` is negative, so the polynomials that have to
be packed have coefficients in `ℤ`.  Packing is still evaluation at the base — the same
homomorphism — but reading the coefficients back needs *balanced* digits: the representative
of `x % b` taken in `(-b/2, b/2)` rather than `[0, b)`.  The overflow condition becomes
`2 * |c| < b`. -/

/-- Evaluate a dense `ℤ`-polynomial at an integer.  This is the signed packing map. -/
@[expose]
def pevZ : List ℤ → ℤ → ℤ
  | [], _ => 0
  | a :: p, b => a + b * pevZ p b

@[simp] lemma pevZ_nil (b : ℤ) : pevZ [] b = 0 := rfl

@[simp] lemma pevZ_cons (a : ℤ) (p : List ℤ) (b : ℤ) :
    pevZ (a :: p) b = a + b * pevZ p b := rfl

/-- The balanced representative of `x` modulo `b`, lying in `(-b/2, b/2)` when `b` is
positive and `x` is a balanced digit. -/
@[expose]
def bdig (b x : ℤ) : ℤ := if 2 * (x % b) < b then x % b else x % b - b

/-- Recover the first `m` balanced digits of a packed `ℤ`-polynomial. -/
@[expose]
def unpackZ (b : ℤ) : ℕ → ℤ → List ℤ
  | 0, _ => []
  | m + 1, x => bdig b x :: unpackZ b m ((x - bdig b x) / b)

@[simp] lemma unpackZ_zero (b x : ℤ) : unpackZ b 0 x = [] := rfl

@[simp] lemma unpackZ_succ (b : ℤ) (m : ℕ) (x : ℤ) :
    unpackZ b (m + 1) x = bdig b x :: unpackZ b m ((x - bdig b x) / b) := rfl

/-- The balanced digit of `c + b * N` is `c`, provided `2 * |c| < b`. -/
lemma bdig_add_mul (b c N : ℤ) (hb : 0 < b) (hc : 2 * |c| < b) :
    bdig b (c + b * N) = c := by
  have hmod : (c + b * N) % b = c % b := Int.add_mul_emod_self_left c b N
  by_cases h : 0 ≤ c
  · rw [abs_of_nonneg h] at hc
    have hcb : c < b := by linarith
    have hx : (c + b * N) % b = c := by rw [hmod, Int.emod_eq_of_lt h hcb]
    simp only [bdig, hx]
    split_ifs
    omega
  · have h' : c < 0 := not_le.1 h
    rw [abs_of_neg h'] at hc
    have hcb : c % b = c + b := by
      have e1 : (c + b) % b = c % b := by simp
      have e2 : (c + b) % b = c + b := Int.emod_eq_of_lt (by linarith) (by linarith)
      omega
    have hx : (c + b * N) % b = c + b := by rw [hmod, hcb]
    simp only [bdig, hx]
    split_ifs <;> omega

/-- **Signed packing is faithful.**  If `2 * |c| < b` for every coefficient `c`, the
coefficients are recovered from the single integer `pevZ p b` by balanced-digit extraction. -/
theorem unpackZ_pevZ (b : ℤ) (hb : 0 < b) :
    ∀ p : List ℤ, (∀ a ∈ p, 2 * |a| < b) → unpackZ b p.length (pevZ p b) = p := by
  intro p
  induction p with
  | nil => intro _; rfl
  | cons a p ih =>
    intro hlt
    have ha : 2 * |a| < b := hlt a (List.mem_cons_self ..)
    have hp : ∀ x ∈ p, 2 * |x| < b := fun x hx => hlt x (List.mem_cons_of_mem _ hx)
    have hd : bdig b (a + b * pevZ p b) = a := bdig_add_mul b a _ hb ha
    have hq : (a + b * pevZ p b - a) / b = pevZ p b := by
      rw [add_sub_cancel_left, Int.mul_ediv_cancel_left _ hb.ne']
    simp only [List.length_cons, pevZ_cons, unpackZ_succ, hd, hq, ih hp]

end Sendov
