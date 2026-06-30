/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Order.Interval.Set.Infinite
public import LeanPool.LeanQuantumAlg.Util.Complex

/-!
# Polynomial helper lemmas (quantum-free)

Generic `ℂ[X]` lemmas used by the QSP development, factored out so they carry
no dependency on the quantum framework:

- `conjP` — coefficient-conjugate of a polynomial (the `P*` of the QSP
  literature) and its ring/eval lemmas;
- `HasParity` — the predicate "all nonzero coefficients sit in degrees of a
  fixed parity" and its closure lemmas;
- total coefficient formulas (`coeff_X_mul'`, `coeff_X_sq_mul`) and bounded
  product-coefficient lemmas;
- `Polynomial.reflect` coefficient/evaluation lemmas;
- `eq_of_circle_eval_eq` — two polynomials agreeing on the unit circle are equal.

These are upstream candidates for Mathlib; nothing here mentions `Gate`/`PureState`.
-/

@[expose] public section

namespace QuantumAlg

open Polynomial Complex

/-! ### Coefficient-conjugate polynomials -/

/-- `conjP P` conjugates every coefficient of `P : ℂ[X]`; this is the `P*` of
the QSP literature (for real `x`, `(conjP P).eval x = conj (P.eval x)`). -/
noncomputable def conjP (P : ℂ[X]) : ℂ[X] := P.map (starRingEnd ℂ)

@[simp]
theorem conjP_coeff (P : ℂ[X]) (k : ℕ) :
    (conjP P).coeff k = starRingEnd ℂ (P.coeff k) :=
  Polynomial.coeff_map _ _

@[simp] theorem conjP_zero : conjP 0 = 0 := Polynomial.map_zero _

@[simp] theorem conjP_one : conjP 1 = 1 := Polynomial.map_one _

@[simp] theorem conjP_X : conjP X = X := Polynomial.map_X _

@[simp]
theorem conjP_C (c : ℂ) : conjP (C c) = C (starRingEnd ℂ c) :=
  Polynomial.map_C _

theorem conjP_add (P Q : ℂ[X]) : conjP (P + Q) = conjP P + conjP Q :=
  Polynomial.map_add _

theorem conjP_sub (P Q : ℂ[X]) : conjP (P - Q) = conjP P - conjP Q :=
  Polynomial.map_sub _

theorem conjP_mul (P Q : ℂ[X]) : conjP (P * Q) = conjP P * conjP Q :=
  Polynomial.map_mul _

theorem conjP_pow (P : ℂ[X]) (n : ℕ) : conjP (P ^ n) = conjP P ^ n :=
  Polynomial.map_pow _ _

@[simp]
theorem conjP_conjP (P : ℂ[X]) : conjP (conjP P) = P := by
  ext k
  simp

/-- Evaluating the coefficient-conjugate at a real point conjugates the value. -/
theorem conjP_eval_ofReal (P : ℂ[X]) (x : ℝ) :
    (conjP P).eval (x : ℂ) = starRingEnd ℂ (P.eval (x : ℂ)) := by
  have h : ((x : ℂ)) = starRingEnd ℂ (x : ℂ) := (Complex.conj_ofReal x).symm
  rw [conjP, Polynomial.eval_map]
  conv_lhs => rw [h]
  rw [Polynomial.eval₂_hom]

/-! ### Parity of polynomials

`HasParity P p` says every nonzero coefficient of `P` sits in a degree
congruent to `p` modulo `2` ("`P` has parity `p mod 2`" in
[Lin22, hermfunc.tex:1132]). The zero polynomial has every parity. -/

/-- All nonzero coefficients of `P` are in degrees `≡ p (mod 2)`. -/
def HasParity (P : ℂ[X]) (p : ℕ) : Prop :=
  ∀ k, P.coeff k ≠ 0 → k % 2 = p % 2

theorem HasParity.coeff_eq_zero {P : ℂ[X]} {p : ℕ} (h : HasParity P p) {k : ℕ}
    (hk : k % 2 ≠ p % 2) : P.coeff k = 0 :=
  by_contra fun hne => hk (h k hne)

theorem hasParity_zero (p : ℕ) : HasParity 0 p := fun k hk => by simp at hk

theorem hasParity_C (c : ℂ) {p : ℕ} (hp : p % 2 = 0) : HasParity (C c) p := by
  intro k hk
  rw [Polynomial.coeff_C] at hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · simp [hp]
  · simp [Nat.pos_iff_ne_zero.mp hpos] at hk

theorem HasParity.add {P Q : ℂ[X]} {p : ℕ} (hP : HasParity P p)
    (hQ : HasParity Q p) : HasParity (P + Q) p := by
  intro k hk
  rw [Polynomial.coeff_add] at hk
  by_cases h : P.coeff k = 0
  · exact hQ k (by simpa [h] using hk)
  · exact hP k h

theorem HasParity.neg {P : ℂ[X]} {p : ℕ} (hP : HasParity P p) :
    HasParity (-P) p := by
  intro k hk
  rw [Polynomial.coeff_neg, neg_ne_zero] at hk
  exact hP k hk

theorem HasParity.sub {P Q : ℂ[X]} {p : ℕ} (hP : HasParity P p)
    (hQ : HasParity Q p) : HasParity (P - Q) p := by
  rw [sub_eq_add_neg]
  exact hP.add hQ.neg

theorem HasParity.C_mul {P : ℂ[X]} {p : ℕ} (c : ℂ) (hP : HasParity P p) :
    HasParity (C c * P) p := by
  intro k hk
  rw [Polynomial.coeff_C_mul] at hk
  exact hP k (right_ne_zero_of_mul hk)

theorem HasParity.conjP {P : ℂ[X]} {p : ℕ} (hP : HasParity P p) :
    HasParity (conjP P) p := by
  intro k hk
  rw [conjP_coeff] at hk
  exact hP k fun h => hk (by simp [h])

/-- Parity only depends on `p` modulo `2`. -/
theorem HasParity.congr {P : ℂ[X]} {p q : ℕ} (hP : HasParity P p)
    (hpq : p % 2 = q % 2) : HasParity P q := by
  intro k hk
  rw [hP k hk, hpq]

/-- Total coefficient formula for `X * P`. -/
theorem coeff_X_mul' (P : ℂ[X]) (n : ℕ) :
    (X * P).coeff n = if n = 0 then 0 else P.coeff (n - 1) := by
  cases n with
  | zero => simp [Polynomial.mul_coeff_zero]
  | succ m => simp [Polynomial.coeff_X_mul]

/-- Total coefficient formula for `X^2 * P`. -/
theorem coeff_X_sq_mul (P : ℂ[X]) (n : ℕ) :
    (X ^ 2 * P).coeff n = if n < 2 then 0 else P.coeff (n - 2) := by
  have h : (X ^ 2 * P : ℂ[X]) = X * (X * P) := by ring
  rw [h, coeff_X_mul' (X * P) n]
  rcases n with - | m
  · simp
  · rw [if_neg (Nat.succ_ne_zero m), Nat.succ_sub_one, coeff_X_mul' P m]
    rcases m with - | l
    · simp
    · have h1 : ¬ (l + 2 < 2) := by omega
      have h2 : l + 2 - 2 = l + 1 - 1 := by omega
      simp [h1, h2]

theorem HasParity.X_mul {P : ℂ[X]} {p : ℕ} (hP : HasParity P p) :
    HasParity (X * P) (p + 1) := by
  intro k hk
  rw [coeff_X_mul'] at hk
  by_cases hk0 : k = 0
  · simp [hk0] at hk
  · rw [if_neg hk0] at hk
    have := hP _ hk
    omega

theorem HasParity.one_sub_X_sq_mul {P : ℂ[X]} {p : ℕ} (hP : HasParity P p) :
    HasParity ((1 - X ^ 2) * P) p := by
  have h : ((1 - X ^ 2) * P : ℂ[X]) = P - X ^ 2 * P := by ring
  rw [h]
  refine hP.sub ?_
  intro k hk
  rw [coeff_X_sq_mul] at hk
  by_cases hk2 : k < 2
  · simp [hk2] at hk
  · rw [if_neg hk2] at hk
    have := hP _ hk
    omega

/-! ### Bounded product coefficients -/

/-- Product coefficient at the sum of two coefficient bounds: only the
top-times-top term survives. -/
theorem coeff_mul_at_bound_add {P Q : ℂ[X]} {a b n : ℕ} (hn : n = a + b)
    (hP : ∀ m, a < m → P.coeff m = 0) (hQ : ∀ m, b < m → Q.coeff m = 0) :
    (P * Q).coeff n = P.coeff a * Q.coeff b := by
  subst hn
  rw [Polynomial.coeff_mul]
  refine Finset.sum_eq_single_of_mem (a, b)
    (Finset.mem_antidiagonal.mpr rfl) (fun c hc hne => ?_)
  rw [Finset.mem_antidiagonal] at hc
  rcases lt_or_ge a c.1 with h1 | h1
  · rw [hP c.1 h1, zero_mul]
  · have h2 : b < c.2 := by
      rcases lt_or_ge b c.2 with h | h
      · exact h
      · exact absurd (Prod.ext (by omega) (by omega)) hne
    rw [hQ c.2 h2, mul_zero]

/-- Product coefficient above the sum of two coefficient bounds vanishes. -/
theorem coeff_mul_eq_zero_of_bound_add {P Q : ℂ[X]} {a b n : ℕ}
    (hn : a + b < n)
    (hP : ∀ m, a < m → P.coeff m = 0) (hQ : ∀ m, b < m → Q.coeff m = 0) :
    (P * Q).coeff n = 0 := by
  rw [Polynomial.coeff_mul]
  refine Finset.sum_eq_zero fun c hc => ?_
  rw [Finset.mem_antidiagonal] at hc
  rcases lt_or_ge a c.1 with h1 | h1
  · rw [hP c.1 h1, zero_mul]
  · rw [hQ c.2 (by omega), mul_zero]

/-! ### Reflection of coefficients -/

theorem coeff_reflect_of_le {F : ℂ[X]} {N m : ℕ} (hm : m ≤ N) :
    (F.reflect N).coeff m = F.coeff (N - m) := by
  rw [Polynomial.coeff_reflect, Polynomial.revAt_le hm]

theorem coeff_reflect_eq_zero {F : ℂ[X]} {N m : ℕ} (hF : F.natDegree ≤ N)
    (hm : N < m) : (F.reflect N).coeff m = 0 := by
  rw [Polynomial.coeff_reflect, Polynomial.revAt_eq_self_of_lt hm]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hF hm)

theorem reflect_sub (F G : ℂ[X]) (N : ℕ) :
    (F - G).reflect N = F.reflect N - G.reflect N := by
  ext k
  simp [Polynomial.coeff_reflect]

theorem reflect_add' (F G : ℂ[X]) (N : ℕ) :
    (F + G).reflect N = F.reflect N + G.reflect N := by
  ext k
  simp [Polynomial.coeff_reflect]

/-- `reflect (L+1) F = X · reflect L F` for `natDegree F ≤ L`. -/
theorem reflect_succ {F : ℂ[X]} {L : ℕ} (hF : F.natDegree ≤ L) :
    F.reflect (L + 1) = X * F.reflect L := by
  ext k
  rw [Polynomial.coeff_reflect, coeff_X_mul']
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [if_pos rfl, Polynomial.revAt_le (Nat.zero_le _)]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  · rw [if_neg (by omega)]
    rcases Nat.lt_or_ge k (L + 2) with hk2 | hk2
    · rw [Polynomial.revAt_le (by omega), Polynomial.coeff_reflect,
        Polynomial.revAt_le (by omega)]
      congr 1
      omega
    · rw [Polynomial.revAt_eq_self_of_lt (by omega), Polynomial.coeff_reflect,
        Polynomial.revAt_eq_self_of_lt (by omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/-- `reflect (L+1) (X·F) = reflect L F` for `natDegree F ≤ L`. -/
theorem reflect_X_mul {F : ℂ[X]} {L : ℕ} (hF : F.natDegree ≤ L) :
    (X * F).reflect (L + 1) = F.reflect L := by
  ext k
  rw [Polynomial.coeff_reflect, Polynomial.coeff_reflect]
  rcases Nat.lt_or_ge k (L + 1) with hk | hk
  · rw [Polynomial.revAt_le (by omega), Polynomial.revAt_le (by omega),
      coeff_X_mul', if_neg (by omega)]
    congr 1
    omega
  · rcases Nat.lt_or_ge k (L + 2) with hk2 | hk2
    · have hkeq : k = L + 1 := by omega
      subst hkeq
      rw [Polynomial.revAt_le le_rfl, Polynomial.revAt_eq_self_of_lt (by omega),
        Nat.sub_self, coeff_X_mul', if_pos rfl,
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    · rw [Polynomial.revAt_eq_self_of_lt (by omega),
        Polynomial.revAt_eq_self_of_lt (by omega), coeff_X_mul',
        if_neg (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/-- Evaluation of a reflection: `(reflect L F)(z) = z^L · F(z⁻¹)`. -/
theorem eval_reflect {F : ℂ[X]} {L : ℕ} (hF : F.natDegree ≤ L) {z : ℂ}
    (hz : z ≠ 0) : (F.reflect L).eval z = z ^ L * F.eval z⁻¹ := by
  have h1 : (F.reflect L).natDegree ≤ L :=
    Polynomial.natDegree_le_iff_degree_le.mpr <|
      (Polynomial.degree_le_iff_coeff_zero _ _).mpr fun m hm =>
        coeff_reflect_eq_zero hF (by exact_mod_cast hm)
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le h1),
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hF), Finset.mul_sum,
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [coeff_reflect_of_le (by omega), show L - (L + 1 - 1 - k) = k by omega,
    show z ^ L = z ^ (L + 1 - 1 - k) * z ^ k by rw [← pow_add]; congr 1; omega,
    inv_pow]
  field_simp

theorem reflect_zero_C (r : ℂ) : (C r).reflect 0 = C r := by
  ext k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Polynomial.coeff_reflect, Polynomial.revAt_le (le_refl 0)]
  · rw [Polynomial.coeff_reflect, Polynomial.revAt_eq_self_of_lt hk]

/-! ### Evaluation on the unit circle -/

/-- Two polynomials agreeing on the unit circle are equal (the circle is an
infinite evaluation set). -/
theorem eq_of_circle_eval_eq {F G : ℂ[X]}
    (h : ∀ x : ℝ, F.eval (Complex.exp ((x : ℂ) * Complex.I))
      = G.eval (Complex.exp ((x : ℂ) * Complex.I))) : F = G := by
  refine Polynomial.eq_of_infinite_eval_eq F G ?_
  refine ((Set.Ioo_infinite Real.pi_pos).image exp_I_injOn_Ioo).mono ?_
  rintro z ⟨x, _, rfl⟩
  exact h x

end QuantumAlg
