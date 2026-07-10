/-
Copyright (c) 2026 Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Tauto

/-!
# Lemma 4.1 for Thakur's hypotheses on power sums
-/

namespace ZetaH123.Lem41

/-
# Problem Description

Fix a prime `p`, an integer `f ≥ 1`, and the prime power `q = p ^ f`. Let `F_q`
be the finite field with `q` elements, and let `A := F_q[t]` be the polynomial
ring in one variable `t`. We work inside the field of formal Laurent series in
`1/t`,
  `F_q((1/t)) ⊇ F_q(t)`,
into which the rational function field `F_q(t)` embeds via expansion of each
rational function as a Laurent series in the uniformizer `1/t` (an expansion in
*descending* powers of `t`).

Concretely, for a monic polynomial `a = t ^ d + θ_1 t ^ {d-1} + … + θ_d` and an
integer `k ≥ 1`, the element `a ^ {-k}` is identified with its expansion
  `a ^ {-k} = t ^ {-dk} (1 + θ_1 t ^ {-1} + … + θ_d t ^ {-d}) ^ {-k} ∈ F_q((1/t))`.

We fix integers `d ≥ 1` and `k > 0`.

## Main Definitions

* Carry-free addition in base `p`: writing each `x_i` in base `p`, the addition
  `x_1 + … + x_r` is carry-free if at every digit position the sum of digits is
  at most `p - 1`.
* The index set `T_{d,k-1}` of `d`-tuples `(m_1,…,m_d)` with `m_i > 0`,
  `(q - 1) ∣ m_i`, and the addition `(k - 1) + m_1 + … + m_d` carry-free in base `p`.
* The weight `w(m) = ∑ i m_i = m_1 + 2 m_2 + … + d m_d`.
* The power sum `S_d(k) = ∑_{a ∈ A_d ^ +} 1/a ^ k`, over monic polynomials of degree
  exactly `d`, viewed in `F_q((1/t))`.

## Main Statement

There exist scalars `c_m ∈ F_q ^ ×` (nonzero), one for each `m ∈ T_{d,k-1}`, with
  `S_d(k) = t ^ {-dk} ∑_{m ∈ T_{d,k-1}} c_m t ^ {-w(m)}`.

Although `T_{d,k-1}` is infinite, the RHS is well defined because only finitely
many `m` satisfy `w(m) ≤ B` for any bound `B`. The claim is about the
tuple-indexed family `(c_m)`: distinct tuples may share the same weight, so after
collecting by power of `t` the coefficient of a given power may be zero in `F_q`
even though every individual `c_m` is nonzero.
-/

open Polynomial

/-! ## Encoding of the Laurent field `F_q((1/t))`

We model `F_q((1/t))` by `LaurentSeries Fq = HahnSeries ℤ Fq`, in which the
formal variable `X` plays the role of the uniformizer `1/t`. Thus `t` corresponds
to `X⁻¹`, and the coefficient of `Xⁿ` of an element is precisely the coefficient
of `t ^ {-n}` in its expansion in descending powers of `t`. -/

/-- The `F_q`-algebra embedding `F_q[t] → F_q((1/t))` sending `t ↦ X⁻¹`, i.e. the
expansion of a polynomial in descending powers of `t`. Since `F_q((1/t))` is a
field, this extends multiplicatively to inverses, which is how `a ^ {-k}` is
interpreted below. -/
noncomputable def phi (Fq : Type) [Field Fq] : Polynomial Fq →ₐ[Fq] LaurentSeries Fq :=
  Polynomial.aeval ((PowerSeries.X : PowerSeries Fq) : LaurentSeries Fq)⁻¹

-- Main Definition(s)

/-- The `e`-th base-`p` digit of `x`, i.e. `⌊x / p ^ e⌋ mod p`. -/
def digit (p x e : ℕ) : ℕ := (x / p ^ e) % p

/-- **Definition 1 (Carry-free addition in base `p`).**
The addition of the nonnegative integers in `xs` is carry-free in base `p` if for
every digit position `e`, the sum of the `e`-th base-`p` digits is at most
`p - 1`. -/
def CarryFree (p : ℕ) (xs : List ℕ) : Prop :=
  ∀ e : ℕ, (xs.map (fun x => digit p x e)).sum ≤ p - 1

/-- The weight `w(m) = ∑ i (m i) = m_1 + 2 m_2 + … + d m_d`.
(Here `m : Fin d → ℕ` is `0`-indexed, so the `i`-th coordinate carries the
multiplier `i + 1`.) -/
def weight (d : ℕ) (m : Fin d → ℕ) : ℕ := ∑ i : Fin d, (i + 1) * m i

/-- **Definition 2 (The index set `T_{d,k-1}`).**
The membership predicate for the set of `d`-tuples `(m_1,…,m_d)` (`0`-indexed as
`m : Fin d → ℕ`) such that:
1. `m i > 0` for all `i`;
2. `(q - 1) ∣ m i` for all `i`;
3. the addition `(k - 1) + m_1 + … + m_d` is carry-free in base `p`. -/
def Tindex (p q d kk : ℕ) (m : Fin d → ℕ) : Prop :=
  (∀ i, 0 < m i) ∧
  (∀ i, (q - 1) ∣ m i) ∧
  CarryFree p (kk :: List.ofFn m)

/-- The monic polynomial of degree exactly `d` with prescribed lower coefficients
`θ : Fin d → Fq`, namely `t ^ d + ∑_{i<d} (θ i) t ^ i`. As `θ` ranges over
`Fin d → Fq` this enumerates the set `A_d ^ +` of monic polynomials of degree `d`
without repetition (see `monicOf_monic`/`monicOf_natDegree`/`monicOf_injective`).
-/
noncomputable def monicOf (Fq : Type) [Field Fq] (d : ℕ) (θ : Fin d → Fq) : Polynomial Fq :=
  X ^ d + ∑ i : Fin d, C (θ i) * X ^ (i : ℕ)

/-- **Definition 3 (The power sum `S_d(k)`).**
`S_d(k) = ∑_{a ∈ A_d ^ +} a ^ {-k}`, summed over the monic polynomials of degree `d`
(parameterized by their lower coefficients `θ : Fin d → Fq`), viewed as an
element of `F_q((1/t))` via the embedding `phi`. The inverse `(phi a)⁻¹` is taken
in the Laurent series field, which realizes the expansion of `a ^ {-1}` in
descending powers of `t`. -/
noncomputable def Sdk (Fq : Type) [Field Fq] [Fintype Fq] (d k : ℕ) : LaurentSeries Fq :=
  ∑ θ : Fin d → Fq, (phi Fq (monicOf Fq d θ))⁻¹ ^ k

-- Main Statement(s)

/-! ## The explicit witness family `c_m`

For a tuple `m = (m_1,…,m_d)` with `y := ∑_i m_i`, the witness coefficient is
  `c_m = (-1) ^ d · (-1) ^ y · C(k+y-1, y) · multinomial(y; m_1,…,m_d)`  (mod `p`),
where the global factor `(-1) ^ d` comes from `∑_{x∈F_q} x ^ {m_i} = -1` for each of
the `d` variables. -/

/-- The explicit witness family. For `m : Fin d → ℕ`, with `y = ∑ i, m i`,
`cwit Fq k m` is the `F_q`-image of the integer
  `(-1) ^ d · (-1) ^ y · C(k + y - 1, y) · multinomial(y; m)`. -/
noncomputable def cwit (Fq : Type) [Field Fq] (d k : ℕ) (m : Fin d → ℕ) : Fq :=
  let y := ∑ i, m i
  ((((-1) ^ d * (-1) ^ y * (Nat.choose (k + y - 1) y : ℤ)
        * (Nat.multinomial Finset.univ m : ℤ)) : ℤ) : Fq)

/-! ## Sub-lemmas of the structure theorem

The proof of `main` factors through: L1 (`Sdk_coeff_as_thetasum`), the
Laurent/multinomial expansion of `coeff n (Sdk)`; L2 (`finField_pow_sum`), the
finite-field power sum collapsing the `θ`-sum; L3/L4
(`negChoose_cast_ne_zero_iff`/`multinomial_cast_ne_zero_iff`), Lucas-type
nonvanishing criteria; L5 (`carryfree_combine`), combining the carry-free
conditions; then the assembly lemmas `cwit_ne_zero` and `Sdk_coeff_eq_finsum`. -/

/-- **L2 (finite-field power sum).** For a finite field `Fq` and `m : ℕ`,
`∑_{x∈Fq} x ^ m = -1` if `m > 0 ∧ (q - 1) ∣ m`, and `= 0` otherwise (`0 ^ 0 = 1`). -/
theorem finField_pow_sum (Fq : Type) [Field Fq] [Fintype Fq] (m : ℕ) :
    (∑ x : Fq, x ^ m) =
      if (0 < m ∧ (Fintype.card Fq - 1) ∣ m) then -1 else 0 := by
  classical
  have hunits : (∑ x : Fqˣ, (x : Fq) ^ m) = ∑ x : {x : Fq // x ≠ 0}, (x : Fq) ^ m := by
    exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun x => rfl)
  have hsplit : (∑ x : Fq, x ^ m) = (0 : Fq) ^ m + ∑ x : {x : Fq // x ≠ 0}, (x : Fq) ^ m := by
    rw [← Fintype.sum_eq_add_sum_subtype_ne (fun x : Fq => x ^ m) 0]
  rw [hsplit, ← hunits, FiniteField.sum_pow_units Fq m]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [pow_zero, lt_irrefl, false_and, if_false]
    rw [if_pos (dvd_zero _)]
    ring
  · rw [zero_pow hm.ne', zero_add]
    simp only [hm, true_and]

/-- **L3 (Lucas, binomial).** The integer `binom(-k, y) = (-1) ^ y · C(k+y-1, y)`
has nonzero image in `F_q` (char `p`) iff the addition `(k - 1) + y` is carry-free
in base `p`, i.e. `CarryFree p [k-1, y]` (Kummer/Lucas). -/
theorem negChoose_cast_ne_zero_iff (Fq : Type) [Field Fq]
    (p k : ℕ) (hp : p.Prime) (hchar : CharP Fq p) (hk : 0 < k) (y : ℕ) :
    (((-1) ^ y * (Nat.choose (k + y - 1) y : ℤ)) : Fq) ≠ 0 ↔
      CarryFree p [k - 1, y] := by
  have hp1 : 1 < p := hp.one_lt
  have step1 : (((-1) ^ y * (Nat.choose (k + y - 1) y : ℤ)) : Fq) ≠ 0 ↔
      ¬ (p ∣ Nat.choose (k+y-1) y) := by
    push_cast
    rw [mul_ne_zero_iff]
    constructor
    · rintro ⟨_, h2⟩ hdvd
      apply h2
      have : ((Nat.choose (k+y-1) y : ℕ) : Fq) = 0 := by
        rw [CharP.cast_eq_zero_iff Fq p]; exact hdvd
      exact this
    · intro hndvd
      refine ⟨pow_ne_zero _ (by simp), ?_⟩
      intro hc
      apply hndvd
      rw [← CharP.cast_eq_zero_iff Fq p]
      exact hc
  rw [step1]
  have hkk : k + y - 1 = (k - 1) + y := by omega
  rw [hkk]
  set N := (k - 1) + y with hN
  have hCpos : Nat.choose N y ≠ 0 := (Nat.choose_pos (by omega : y ≤ N)).ne'
  have step3 : ¬ (p ∣ Nat.choose N y) ↔ (Nat.choose N y).factorization p = 0 := by
    rw [Nat.factorization_eq_zero_iff]
    constructor
    · intro h; right; left; exact h
    · rintro (h|h|h)
      · exact absurd hp h
      · exact h
      · exact absurd h hCpos
  rw [step3]
  set b := Nat.log p N + 1 with hb
  have hbgt : Nat.log p N < b := by omega
  have hfact := Nat.factorization_choose' (p := p) (n := k-1) (k := y) hp (by rw [← hN]; exact hbgt)
  rw [← hN] at hfact
  rw [hfact]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  have bridge : (∀ i ∈ Finset.Ico 1 b, ¬ (p ^ i ≤ y % p ^ i + (k - 1) % p ^ i)) ↔
      (∀ i, 1 ≤ i → y % p ^ i + (k - 1) % p ^ i < p ^ i) := by
    constructor
    · intro Hf i hi
      by_cases hib : i < b
      · have := Hf i (Finset.mem_Ico.mpr ⟨hi, hib⟩); omega
      · push Not at hib
        have hilog : Nat.log p N < i := lt_of_lt_of_le hbgt hib
        have hNlt : N < p ^ i := by
          calc N < p ^ (Nat.log p N + 1) := Nat.lt_pow_succ_log_self hp1 _
            _ ≤ p ^ i := Nat.pow_le_pow_right (by omega) (by omega)
        have hy : y < p ^ i := by omega
        have hk1 : k-1 < p ^ i := by omega
        rw [Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hk1]; omega
    · intro H i hi hle
      rw [Finset.mem_Ico] at hi
      have := H i hi.1; omega
  rw [bridge]
  change (∀ i, 1 ≤ i → y % p ^ i + (k - 1) % p ^ i < p ^ i) ↔ CarryFree p [k-1, y]
  unfold CarryFree digit
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  constructor
  · intro H e
    have hi := H (e + 1) (by omega)
    have hpe : 0 < p ^ e := Nat.pow_pos (n := e) (by omega)
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ, pow_succ] at hi
    have hae : y % p ^ e < p ^ e := Nat.mod_lt _ hpe
    have hbe : (k - 1) % p ^ e < p ^ e := Nat.mod_lt _ hpe
    generalize hA : y % p ^ e = A at *
    generalize hB : (k - 1) % p ^ e = B at *
    generalize hu : y / p ^ e % p = u at *
    generalize hv : (k - 1) / p ^ e % p = v at *
    set Pe := p ^ e
    by_contra hcon
    push Not at hcon
    have hge : p ≤ v + u := by omega
    have hmul : Pe * p ≤ Pe * (v + u) := Nat.mul_le_mul_left _ hge
    have hexp : Pe * (v + u) = Pe * v + Pe * u := by ring
    omega
  · intro H
    have hno : ∀ e, y % p ^ e + (k - 1) % p ^ e < p ^ e := by
      intro e
      induction e with
      | zero => simp [Nat.mod_one]
      | succ e ih =>
        have hpe : 0 < p ^ e := Nat.pow_pos (n := e) (by omega)
        have hda := H e
        rw [Nat.mod_pow_succ, Nat.mod_pow_succ, pow_succ]
        generalize hA : y % p ^ e = A at *
        generalize hB : (k - 1) % p ^ e = B at *
        generalize hu : y / p ^ e % p = u at *
        generalize hv : (k - 1) / p ^ e % p = v at *
        set Pe := p ^ e
        have h1 : Pe * u + Pe * v = Pe * (u+v) := by ring
        have h2 : Pe * (u+v) ≤ Pe * (p-1) := Nat.mul_le_mul_left _ (by omega)
        have h3 : Pe * (p-1) = Pe*p - Pe := by rw [Nat.mul_sub_one]
        have h4 : Pe ≤ Pe * p := Nat.le_mul_of_pos_right _ (by omega)
        omega
    intro i _
    exact hno i

/-- **L4 (Lucas, multinomial).** With `y = ∑ i, m i`, the multinomial coefficient
`multinomial(y; m_1,…,m_d)` has nonzero image in `F_q` iff the addition
`m_1 ⊕ m_2 ⊕ … ⊕ m_d` is carry-free in base `p`, i.e. `CarryFree p (List.ofFn m)`.
(Telescoping product of binomial-Lucas, informal.tex Lemma 1.6.) -/
theorem multinomial_cast_ne_zero_iff (Fq : Type) [Field Fq]
    (p d : ℕ) (hp : p.Prime) (hchar : CharP Fq p) (m : Fin d → ℕ) :
    ((Nat.multinomial Finset.univ m : ℤ) : Fq) ≠ 0 ↔
      CarryFree p (List.ofFn m) := by
  -- Binomial cast characterization (from L3): `C(a+s, a) ≠ 0` in `Fq` iff
  -- `CarryFree p [a, s]`.
  have hbinom : ∀ a s : ℕ, ((Nat.choose (a + s) a : ℤ) : Fq) ≠ 0 ↔ CarryFree p [a, s] := by
    intro a s
    have h3 := negChoose_cast_ne_zero_iff Fq p (a+1) hp hchar (by omega) s
    have he1 : (a + 1) + s - 1 = a + s := by omega
    have he2 : Nat.choose (a + s) s = Nat.choose (a + s) a := by
      have := Nat.choose_symm (n := a + s) (k := a) (by omega)
      rw [show a + s - a = s by omega] at this
      exact this
    rw [he1, he2] at h3
    have hsimp : (a + 1) - 1 = a := by omega
    rw [hsimp] at h3
    rw [← h3]
    push_cast
    have hu : ((-1:Fq)) ^ s ≠ 0 := pow_ne_zero _ (by simp)
    rw [mul_ne_zero_iff]
    tauto
  -- Product of factorials divides factorial of sum (so the list multinomial is an
  -- integer).
  have hmultidvd : ∀ L : List ℕ, (L.map Nat.factorial).prod ∣ L.sum.factorial := by
    intro L
    induction L with
    | nil => simp
    | cons a t ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      calc a.factorial * (t.map Nat.factorial).prod
          ∣ a.factorial * t.sum.factorial := Nat.mul_dvd_mul_left _ ih
        _ ∣ (a + t.sum).factorial := Nat.factorial_mul_factorial_dvd_factorial_add a t.sum
  -- Recurrence for the list multinomial: peeling off the head gives a binomial
  -- factor.
  have hrec : ∀ (a : ℕ) (L : List ℕ),
      (a + L.sum).factorial / ((a :: L).map Nat.factorial).prod
        = (a + L.sum).choose a * (L.sum.factorial / (L.map Nat.factorial).prod) := by
    intro a L
    have hprodpos : 0 < (L.map Nat.factorial).prod := by
      apply List.prod_pos
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨n, _, rfl⟩ := hx
      exact Nat.factorial_pos n
    have key : (a + L.sum).factorial = (a + L.sum).choose a * (a.factorial * L.sum.factorial) := by
      have h := Nat.add_choose_mul_factorial_mul_factorial L.sum a
      rw [add_comm L.sum a] at h
      rw [← h]; ring
    simp only [List.map_cons, List.prod_cons]
    rw [key]
    obtain ⟨c, hc⟩ := hmultidvd L
    rw [hc]
    have e1 :
        (a + L.sum).choose a * (a.factorial * ((L.map Nat.factorial).prod * c))
            / (a.factorial * (L.map Nat.factorial).prod)
          = (a + L.sum).choose a * c := by
      rw [show (a + L.sum).choose a * (a.factorial * ((L.map Nat.factorial).prod * c))
          = ((a + L.sum).choose a * c) * (a.factorial * (L.map Nat.factorial).prod) by
        ring]
      rw [Nat.mul_div_cancel _ (by positivity)]
    rw [e1, Nat.mul_div_cancel_left _ hprodpos]
  -- Inlined crux machinery (the `crux_*` lemmas appear later in the file).
  have crux_div : ∀ (a b : ℕ), 1 < p → (∀ e, digit p a e + digit p b e ≤ p - 1) →
      ∀ e, (a + b) / p ^ e = a / p ^ e + b / p ^ e := by
    intro a b hp h e
    induction e with
    | zero => simp
    | succ e ih =>
      rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
      rw [ih]
      have hdig : (a / p ^ e) % p + (b / p ^ e) % p ≤ p - 1 := h e
      have key : (a / p ^ e + b / p ^ e)
          = p * (a / p ^ e / p + b / p ^ e / p)
            + ((a / p ^ e) % p + (b / p ^ e) % p) := by
        have ha := Nat.div_add_mod (a / p ^ e) p
        have hb := Nat.div_add_mod (b / p ^ e) p
        ring_nf; omega
      rw [key, Nat.mul_add_div (by omega : 0 < p)]
      have hz : ((a / p ^ e) % p + (b / p ^ e) % p) / p = 0 := Nat.div_eq_of_lt (by omega)
      omega
  have crux_digit_two : ∀ (a b : ℕ), 1 < p → (∀ e, digit p a e + digit p b e ≤ p - 1) →
      ∀ e, digit p (a + b) e = digit p a e + digit p b e := by
    intro a b hp h e
    have hd := crux_div a b hp h e
    have hb := h e
    unfold digit at *
    rw [hd, Nat.add_mod]
    have h1 : (a / p ^ e) % p % p = (a / p ^ e) % p := Nat.mod_mod_of_dvd _ dvd_rfl
    have h2 : (b / p ^ e) % p % p = (b / p ^ e) % p := Nat.mod_mod_of_dvd _ dvd_rfl
    rw [Nat.mod_eq_of_lt (show (a / p ^ e) % p + (b / p ^ e) % p < p by omega)]
  have crux_list : ∀ (L : List ℕ), (∀ e, (L.map (fun x => digit p x e)).sum ≤ p - 1) →
      ∀ e, digit p L.sum e = (L.map (fun x => digit p x e)).sum := by
    intro L
    rcases Nat.lt_or_ge p 2 with hpp | hpp
    · interval_cases p
      · intro h e
        rcases Nat.eq_zero_or_pos e with he | he
        · subst he
          have hd : ∀ x : ℕ, digit 0 x 0 = x := by intro x; unfold digit; simp
          rw [hd]
          conv_rhs => rw [show (fun x => digit 0 x 0) = (id : ℕ → ℕ) by funext x; simp [hd]]
          simp
        · unfold digit
          have h0 : (0:ℕ) ^ e = 0 := by simp [Nat.pow_eq_zero]; omega
          simp only [h0, Nat.div_zero, Nat.zero_mod, List.map_const', List.sum_replicate,
            smul_eq_mul, mul_zero]
      · intro h e
        have hd : ∀ x : ℕ, digit 1 x e = 0 := by intro x; unfold digit; simp [Nat.mod_one]
        simp [hd]
    · have hp' : 1 < p := hpp
      intro h
      induction L with
      | nil => intro e; simp [digit]
      | cons a t ih =>
        have htail : ∀ e, (t.map (fun x => digit p x e)).sum ≤ p - 1 := by
          intro e; have := h e; simp only [List.map_cons, List.sum_cons] at this; omega
        have ihd := ih htail
        intro e
        simp only [List.map_cons, List.sum_cons]
        have hpair : ∀ e, digit p a e + digit p t.sum e ≤ p - 1 := by
          intro e
          rw [ihd e]
          have := h e
          simp only [List.map_cons, List.sum_cons] at this
          exact this
        rw [crux_digit_two a t.sum hp' hpair e, ihd e]
  -- CarryFree splits over a cons: the head together with the tail-sum.
  have hcons : ∀ (a : ℕ) (L : List ℕ),
      (CarryFree p [a, L.sum] ∧ CarryFree p L) ↔ CarryFree p (a :: L) := by
    intro a L
    unfold CarryFree
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    constructor
    · rintro ⟨h1, h2⟩ e
      have hc := crux_list L h2 e
      have h1e := h1 e
      rw [hc] at h1e
      exact h1e
    · intro h
      have h2 : ∀ e, (L.map (fun x => digit p x e)).sum ≤ p - 1 := by
        intro e; have := h e; omega
      refine ⟨?_, h2⟩
      intro e
      have hc := crux_list L h2 e
      have he := h e
      rw [← hc] at he
      exact he
  -- Main induction on lists: the list multinomial cast is nonzero iff CarryFree.
  have hmain : ∀ L : List ℕ,
      (((L.sum.factorial / (L.map Nat.factorial).prod : ℕ) : ℤ) : Fq) ≠ 0 ↔ CarryFree p L := by
    intro L
    induction L with
    | nil =>
      simp only [List.sum_nil, List.map_nil, List.prod_nil, Nat.factorial_zero]
      constructor
      · intro _ e; simp [digit]
      · intro _; simp
    | cons a t ih =>
      have hrr := hrec a t
      rw [List.sum_cons]
      have hcast : (((a + t.sum).factorial / ((a :: t).map Nat.factorial).prod : ℕ) : Fq)
          = ((a + t.sum).choose a : Fq)
            * ((t.sum.factorial / (t.map Nat.factorial).prod : ℕ) : Fq) := by
        rw [hrr]; push_cast; ring
      rw [Int.cast_natCast, hcast]
      rw [mul_ne_zero_iff]
      have hb := hbinom a t.sum
      rw [Int.cast_natCast] at hb
      rw [hb]
      rw [show (((t.sum.factorial / (t.map Nat.factorial).prod : ℕ) : Fq))
          = ((((t.sum.factorial / (t.map Nat.factorial).prod : ℕ) : ℤ)) : Fq) by
        rw [Int.cast_natCast]] at *
      rw [ih]
      rw [hcons a t]
  -- Reduce `Nat.multinomial Finset.univ m` to the list version over `List.ofFn m`.
  have hreduce : ((Nat.multinomial Finset.univ m : ℤ) : Fq)
      = ((((List.ofFn m).sum.factorial
          / ((List.ofFn m).map Nat.factorial).prod : ℕ) : ℤ) : Fq) := by
    unfold Nat.multinomial
    rw [List.sum_ofFn]
    norm_cast
    congr 2
    rw [List.map_ofFn, List.prod_ofFn]
    rfl
  rw [hreduce, hmain]

/-- Crux (division form). If, at every base-`p` digit position, the digits of `a`
and `b` sum to at most `p - 1` (no carry), then dividing by `p ^ e` distributes
over the sum `a + b`. Requires `1 < p`. -/
theorem crux_div (p a b : ℕ) (hp : 1 < p)
    (h : ∀ e, digit p a e + digit p b e ≤ p - 1) :
    ∀ e, (a + b) / p ^ e = a / p ^ e + b / p ^ e := by
  intro e
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
    rw [ih]
    have hdig : (a / p ^ e) % p + (b / p ^ e) % p ≤ p - 1 := h e
    have key : (a / p ^ e + b / p ^ e)
        = p * (a / p ^ e / p + b / p ^ e / p)
          + ((a / p ^ e) % p + (b / p ^ e) % p) := by
      have ha := Nat.div_add_mod (a / p ^ e) p
      have hb := Nat.div_add_mod (b / p ^ e) p
      ring_nf; omega
    rw [key, Nat.mul_add_div (by omega : 0 < p)]
    have hz : ((a / p ^ e) % p + (b / p ^ e) % p) / p = 0 := Nat.div_eq_of_lt (by omega)
    omega

/-- Crux (two-summand digit form). Under the no-carry hypothesis, the digit of the
sum equals the sum of digits at every position. -/
theorem crux_digit_two (p a b : ℕ) (hp : 1 < p)
    (h : ∀ e, digit p a e + digit p b e ≤ p - 1) :
    ∀ e, digit p (a + b) e = digit p a e + digit p b e := by
  intro e
  have hd := crux_div p a b hp h e
  have hb := h e
  unfold digit at *
  rw [hd, Nat.add_mod]
  have h1 : (a / p ^ e) % p % p = (a / p ^ e) % p := Nat.mod_mod_of_dvd _ dvd_rfl
  have h2 : (b / p ^ e) % p % p = (b / p ^ e) % p := Nat.mod_mod_of_dvd _ dvd_rfl
  rw [Nat.mod_eq_of_lt (show (a / p ^ e) % p + (b / p ^ e) % p < p by omega)]

/-- Crux (list form, all `p`). If the addition of the entries of `L` is carry-free
in base `p`, then for every digit position the digit of `L.sum` equals the sum of
the digits of the entries. (Holds unconditionally for `p ≤ 1`.) -/
theorem crux_list (p : ℕ) (L : List ℕ)
    (h : ∀ e, (L.map (fun x => digit p x e)).sum ≤ p - 1) :
    ∀ e, digit p L.sum e = (L.map (fun x => digit p x e)).sum := by
  rcases Nat.lt_or_ge p 2 with hp | hp
  · interval_cases p
    · intro e
      rcases Nat.eq_zero_or_pos e with he | he
      · subst he
        have hd : ∀ x : ℕ, digit 0 x 0 = x := by intro x; unfold digit; simp
        rw [hd]
        conv_rhs => rw [show (fun x => digit 0 x 0) = (id : ℕ → ℕ) by funext x; simp [hd]]
        simp
      · unfold digit
        have h0 : (0:ℕ) ^ e = 0 := by simp [Nat.pow_eq_zero]; omega
        simp only [h0, Nat.div_zero, Nat.zero_mod, List.map_const', List.sum_replicate,
          smul_eq_mul, mul_zero]
    · intro e
      have hd : ∀ x : ℕ, digit 1 x e = 0 := by intro x; unfold digit; simp [Nat.mod_one]
      simp [hd]
  · have hp' : 1 < p := hp
    induction L with
    | nil => intro e; simp [digit]
    | cons a t ih =>
      have htail : ∀ e, (t.map (fun x => digit p x e)).sum ≤ p - 1 := by
        intro e; have := h e; simp only [List.map_cons, List.sum_cons] at this; omega
      have ihd := ih htail
      intro e
      simp only [List.map_cons, List.sum_cons]
      have hpair : ∀ e, digit p a e + digit p t.sum e ≤ p - 1 := by
        intro e
        rw [ihd e]
        have := h e
        simp only [List.map_cons, List.sum_cons] at this
        exact this
      rw [crux_digit_two p a t.sum hp' hpair e, ihd e]

/-- **L5 (carry-free combination).** With `y = ∑ i, m i`, the two carry-free
conditions `CarryFree p [k-1, y]` (binomial) and `CarryFree p (List.ofFn m)`
(multinomial) hold simultaneously iff the combined addition is carry-free, i.e.
`CarryFree p ((k - 1) :: List.ofFn m)`. -/
theorem carryfree_combine (p kk d : ℕ) (m : Fin d → ℕ) :
    (CarryFree p [kk, ∑ i, m i] ∧ CarryFree p (List.ofFn m)) ↔
      CarryFree p (kk :: List.ofFn m) := by
  have hsum : (List.ofFn m).sum = ∑ i, m i := by rw [List.sum_ofFn]
  unfold CarryFree
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  constructor
  · rintro ⟨h1, h2⟩ e
    have hc := crux_list p (List.ofFn m) h2 e
    rw [hsum] at hc
    have h1e := h1 e
    rw [hc] at h1e
    exact h1e
  · intro h
    have h2 : ∀ e, ((List.ofFn m).map (fun x => digit p x e)).sum ≤ p - 1 := by
      intro e; have := h e; omega
    refine ⟨?_, h2⟩
    intro e
    have hc := crux_list p (List.ofFn m) h2 e
    rw [hsum] at hc
    have he := h e
    rw [← hc] at he
    exact he

/-! ### L1 helper lemmas (PowerSeries / LaurentSeries infrastructure)

The proof of L1 (`Sdk_coeff_as_thetasum`) is decomposed into helper lemmas H1–H5:
H1 is the generalized binomial / unit-inverse power-series expansion; H2–H4 are
the `phi`/`monicOf` → LaurentSeries bridge and the HahnSeries shift; H5 is the
finite-vs-finsum bookkeeping. -/

/-- **H1 (generalized binomial / unit-inverse power-series expansion).** For a
power series `g` with zero constant term, the `e`-th coefficient of
`((1 + g) ^ k)⁻¹` is the finite sum `∑_{y ≤ e} binom(-k, y) · coeff_e (g ^ y)`,
where `binom(-k, y) = (-1) ^ y · C(k+y-1, y)`. (Only `y ≤ e` contribute since
`order (g ^ y) ≥ y`.) -/
theorem coeff_inv_one_add_pow
    (Fq : Type) [Field Fq] (k e : ℕ) (g : PowerSeries Fq)
    (hg : PowerSeries.constantCoeff (R := Fq) g = 0) :
    (PowerSeries.coeff (R := Fq) e) (((1 + g) ^ k)⁻¹) =
      ∑ y ∈ Finset.range (e + 1),
        ((-1) ^ y * (Nat.choose (k + y - 1) y : ℤ) : Fq)
          * (PowerSeries.coeff (R := Fq) e) (g ^ y) := by
  -- Substitute `X ↦ -g` into `mk_add_choose_mul_one_sub_pow_eq_one`, extract the
  -- `e`-th coefficient via `coeff_subst'`, and truncate the finsum to `range (e + 1)`.
  have coeff_pow_high : ∀ d : ℕ, e < d → (PowerSeries.coeff (R := Fq) e) (g ^ d) = 0 := by
    intro d h
    apply PowerSeries.coeff_of_lt_order
    have h1 : 1 ≤ g.order := PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hg
    have h2 : (d : ℕ∞) ≤ (g ^ d).order := by
      rw [PowerSeries.order_pow]
      calc (d : ℕ∞) = d • (1 : ℕ∞) := by simp
        _ ≤ d • g.order := by gcongr
    calc (e : ℕ∞) < d := by exact_mod_cast h
      _ ≤ (g ^ d).order := h2
  have coeff_neg_pow : ∀ d : ℕ,
      (PowerSeries.coeff (R := Fq) e) ((-g) ^ d)
        = (-1) ^ d * (PowerSeries.coeff (R := Fq) e) (g ^ d) := by
    intro d
    rcases Nat.even_or_odd d with hd | hd
    · rw [hd.neg_pow, hd.neg_one_pow, one_mul]
    · rw [hd.neg_pow, hd.neg_one_pow, map_neg, neg_one_mul]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [pow_zero, inv_one]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro y _ hy
      have hz : Nat.choose (0 + y - 1) y = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hz]; simp
    · intro h; simp at h
  · obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_lt hk
    rw [Nat.zero_add] at *
    have ha : PowerSeries.HasSubst (-g : PowerSeries Fq) := by
      apply PowerSeries.HasSubst.of_constantCoeff_zero'
      simp [hg]
    have hinv : (((1 + g) ^ (k'+1))⁻¹) =
        PowerSeries.subst (-g) (PowerSeries.mk fun n => ((k' + n).choose k' : Fq)) := by
      have hkey := PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one Fq k'
      set S := PowerSeries.substAlgHom (R := Fq) ha with hS
      have happ := congrArg S hkey
      rw [map_mul, map_one] at happ
      have h1 : S ((1 - PowerSeries.X) ^ (k'+1)) = (1 + g) ^ (k'+1) := by
        rw [map_pow, map_sub, map_one, hS, PowerSeries.coe_substAlgHom,
          PowerSeries.subst_X ha]
        ring
      rw [h1] at happ
      rw [hS, PowerSeries.coe_substAlgHom] at happ
      rw [PowerSeries.inv_eq_iff_mul_eq_one]
      · exact happ
      · rw [map_pow]; simp [hg]
    rw [hinv, PowerSeries.coeff_subst' ha]
    rw [finsum_eq_finsetSum_of_support_subset _ (s := Finset.range (e + 1))]
    · apply Finset.sum_congr rfl
      intro d hd
      rw [PowerSeries.coeff_mk, coeff_neg_pow, smul_eq_mul]
      have hnat : (k' + d).choose k' = ((k'+1) + d - 1).choose d := by
        have h : (k'+1) + d - 1 = k' + d := by omega
        rw [h, Nat.choose_symm_add]
      rw [hnat]; push_cast; ring
    · intro d hd
      simp only [Function.mem_support] at hd
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hcon
      push Not at hcon
      apply hd
      rw [PowerSeries.coeff_mk, coeff_neg_pow, coeff_pow_high d (by omega)]
      simp

/-- **H2 (`phi (monicOf θ)` made explicit).** `phi (monicOf θ)` equals the shift
`single (-d) 1` times the coercion of the unit power series
`1 + ∑_{i<d} θ_i X ^ {d-i}`. (`phi = aeval X⁻¹`, `X⁻¹ = single (-1) 1`; pull out
`single (-d) 1` and identify the bracket with the coerced power series.) -/
theorem phi_monicOf_eq (Fq : Type) [Field Fq] (d : ℕ) (θ : Fin d → Fq) :
    phi Fq (monicOf Fq d θ)
      = (HahnSeries.single (-(d : ℤ)) 1)
          * (HahnSeries.ofPowerSeries ℤ Fq
              (1 + ∑ i : Fin d,
                (PowerSeries.C (R := Fq) (θ i)) * PowerSeries.X ^ (d - (i : ℕ)))) := by
  have hpow : ∀ (n : ℕ) (a : ℤ),
      (HahnSeries.single a (1 : Fq)) ^ n = HahnSeries.single (n * a) 1 := by
    intro n a
    induction n with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, HahnSeries.single_mul_single]
      congr 1 <;> push_cast <;> ring_nf
  have hXinv :
      ((PowerSeries.X : PowerSeries Fq) : LaurentSeries Fq)⁻¹ = HahnSeries.single (-1) 1 := by
    apply inv_eq_of_mul_eq_one_left
    rw [PowerSeries.coe_X, HahnSeries.single_mul_single]; norm_num
  have halg : ∀ a : Fq, algebraMap Fq (LaurentSeries Fq) a = HahnSeries.single 0 a := by
    intro a
    rw [LaurentSeries.algebraMap_apply, HahnSeries.C_apply]
  have hofX : ∀ m : ℕ,
      HahnSeries.ofPowerSeries ℤ Fq (PowerSeries.X ^ m) = HahnSeries.single (m : ℤ) 1 := by
    intro m
    rw [map_pow, PowerSeries.coe_X, hpow]; congr 1; simp
  have hLHSterm : ∀ i : Fin d,
      (Polynomial.aeval ((HahnSeries.single (-1) 1 : LaurentSeries Fq)))
          (Polynomial.C (θ i) * Polynomial.X ^ (i : ℕ))
        = HahnSeries.single (-(i : ℤ)) (θ i) := by
    intro i
    rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, hpow, halg,
        HahnSeries.single_mul_single]
    congr 1 <;> ring_nf
  have hRHSterm : ∀ i : Fin d,
      (HahnSeries.single (-(d : ℤ)) (1 : Fq)) *
          (HahnSeries.ofPowerSeries ℤ Fq
            ((PowerSeries.C (R := Fq) (θ i)) * PowerSeries.X ^ (d - (i : ℕ))))
        = HahnSeries.single (-(i : ℤ)) (θ i) := by
    intro i
    rw [map_mul, hofX, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply,
        ← mul_assoc, HahnSeries.single_mul_single, HahnSeries.single_mul_single, mul_one, one_mul]
    congr 1
    have : (i : ℕ) ≤ d := le_of_lt i.isLt
    push_cast [Nat.cast_sub this]
    ring_nf
  -- LHS transform
  unfold phi monicOf
  rw [map_add, map_pow, map_sum, Polynomial.aeval_X, hXinv, hpow,
      show ((d : ℤ) * (-1)) = -(d : ℤ) by ring]
  rw [Finset.sum_congr rfl (fun i _ => hLHSterm i)]
  -- RHS transform
  rw [map_add, mul_add, map_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun i _ => hRHSterm i)]
  -- now: single(-d)1 + ∑ single(-i)(θi) = single(-d)1 * ofPowerSeries 1 + ∑ single(-i)(θi)
  congr 1
  simp

/-- **H3 (inverse `k`-th power as shift × PowerSeries inverse).** From H2: the
`k`-th power of the inverse is `single (d*k) 1` times the coercion of the
PowerSeries inverse `((1 + g) ^ k)⁻¹`, where `g = ∑_{i<d} θ_i X ^ {d-i}`. Uses that a
power series with constant term `1` is a unit, so `(↑u)⁻¹ = ↑(u⁻¹)` in
`LaurentSeries`. -/
theorem inv_phi_pow_eq_shift_mul (Fq : Type) [Field Fq] (d k : ℕ) (θ : Fin d → Fq) :
    (phi Fq (monicOf Fq d θ))⁻¹ ^ k
      = (HahnSeries.single (d * k : ℤ) 1)
          * (HahnSeries.ofPowerSeries ℤ Fq
              (((1 + ∑ i : Fin d,
                (PowerSeries.C (R := Fq) (θ i)) * PowerSeries.X ^ (d - (i : ℕ))) ^ k)⁻¹)) := by
  set u : PowerSeries Fq :=
    1 + ∑ i : Fin d, (PowerSeries.C (R := Fq) (θ i)) * PowerSeries.X ^ (d - (i : ℕ)) with hu
  -- u has constant term 1, hence is a unit in PowerSeries
  have hconst : PowerSeries.constantCoeff (R := Fq) u = 1 := by
    rw [hu]
    simp only [map_add, map_one, map_sum, map_mul, map_pow, PowerSeries.constantCoeff_X]
    have : ∀ i : Fin d, (PowerSeries.constantCoeff (R := Fq) (PowerSeries.C (R := Fq) (θ i)))
        * (0 : Fq) ^ (d - (i : ℕ)) = 0 := by
      intro i
      have : d - (i : ℕ) ≠ 0 := by omega
      rw [zero_pow this, mul_zero]
    rw [Finset.sum_eq_zero (fun i _ => this i), add_zero]
  have hunit : IsUnit u := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hconst]; exact isUnit_one
  -- the LaurentSeries coercion of u is a unit
  have hofu_unit : IsUnit (HahnSeries.ofPowerSeries ℤ Fq u) :=
    hunit.map (HahnSeries.ofPowerSeries ℤ Fq)
  have hofu_ne : (HahnSeries.ofPowerSeries ℤ Fq u) ≠ 0 := hofu_unit.ne_zero
  -- single(-d)1 is a unit with inverse single(d)1
  have hsingle_ne : (HahnSeries.single (-(d : ℤ)) (1 : Fq)) ≠ 0 := by
    simp
  have hpow : ∀ (n : ℕ) (a : ℤ),
      (HahnSeries.single a (1 : Fq)) ^ n = HahnSeries.single (n * a) 1 := by
    intro n a
    induction n with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ih, HahnSeries.single_mul_single]
      congr 1 <;> push_cast <;> ring_nf
  -- rewrite phi via H2
  rw [phi_monicOf_eq, ← hu]
  rw [mul_inv_rev, mul_pow]
  -- handle the single factor: (single(-d)1)⁻¹ ^ k = single(d*k)1
  have hsingle :
      (HahnSeries.single (-(d : ℤ)) (1 : Fq))⁻¹ ^ k =
        HahnSeries.single (d * k : ℤ) 1 := by
    have hinv : (HahnSeries.single (-(d : ℤ)) (1 : Fq))⁻¹ = HahnSeries.single (d : ℤ) 1 := by
      apply inv_eq_of_mul_eq_one_left
      rw [HahnSeries.single_mul_single]; norm_num
    rw [hinv, hpow]; congr 1; ring_nf
  rw [mul_comm ((HahnSeries.ofPowerSeries ℤ Fq u)⁻¹ ^ k) _, hsingle]
  congr 1
  -- ofPS(u)⁻¹ ^ k = ofPS((u ^ k)⁻¹)
  rw [inv_pow, ← map_pow]
  -- u ^ k has nonzero constant term, so (u ^ k)⁻¹ * u ^ k = 1 in PowerSeries
  have hck : PowerSeries.constantCoeff (R := Fq) (u ^ k) ≠ 0 := by
    rw [map_pow, hconst, one_pow]; exact one_ne_zero
  apply inv_eq_of_mul_eq_one_left
  rw [← map_mul, PowerSeries.inv_mul_cancel _ hck, map_one]

/-- **H4 (coefficient of `single s 1 * ↑f`, the Laurent shift).** The `n`-th
coefficient of `single s 1 * (↑f)` is the `(n-s)`-th PowerSeries coefficient of
`f` when `n - s ≥ 0`, else `0`. -/
theorem coeff_single_mul_coe_powerSeries
    (Fq : Type) [Field Fq] (s : ℤ) (f : PowerSeries Fq) (n : ℤ) :
    ((HahnSeries.single s 1 * (HahnSeries.ofPowerSeries ℤ Fq f)) : LaurentSeries Fq).coeff n
      = if _h : 0 ≤ n - s then (PowerSeries.coeff (R := Fq) (n - s).toNat) f else 0 := by
  rw [HahnSeries.coeff_single_mul, one_mul]
  split
  · next _h =>
    conv_lhs => rw [show (n - s) = ((n - s).toNat : ℤ) by omega]
    rw [LaurentSeries.coeff_coe_powerSeries]
  · next h =>
    rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
    rintro ⟨m, hm⟩
    simp at hm
    omega

/-- **H5 (per-`θ` coefficient identity).** Assembling H1 (binomial expansion),
the multinomial theorem (`Finset.sum_pow_eq_sum_piAntidiag` for `g ^ y`), and the
re-indexing of the `X ^ {d-i}` exponents against `weight d m = ∑ (i+1) m_i`, the
coefficient of `X ^ n` in `(phi (monicOf θ))⁻¹ ^ k` is the finsum over tuples `m` with
`d*k + weight(m) = n` of `binom(-k, ∑ m_i)·multinomial·∏ θ_i ^ {m_i}`. -/
theorem Sdk_coeff_per_theta (Fq : Type) [Field Fq] (d k : ℕ) (θ : Fin d → Fq) (n : ℤ) :
    ((phi Fq (monicOf Fq d θ))⁻¹ ^ k).coeff n =
      ∑ᶠ m ∈ {m : Fin d → ℕ | ((d * k : ℕ) + weight d m : ℤ) = n},
        ((-1) ^ (∑ i, m i) * (Nat.choose (k + (∑ i, m i) - 1) (∑ i, m i) : ℤ)
            * (Nat.multinomial Finset.univ m : ℤ) : Fq)
          * ∏ i, (θ (Fin.rev i)) ^ (m i) := by
  -- The coordinate `θ i` carries X-exponent `d - i`, not `i + 1`, so the correct
  -- pairing against `m i` (whence `weight`) is `θ (Fin.rev i)`.
  rw [inv_phi_pow_eq_shift_mul, coeff_single_mul_coe_powerSeries]
  set g : PowerSeries Fq :=
    ∑ i : Fin d, (PowerSeries.C (R := Fq) (θ i)) * PowerSeries.X ^ (d - (i : ℕ)) with hgdef
  have hg : PowerSeries.constantCoeff (R := Fq) g = 0 := by
    rw [hgdef]
    simp only [map_sum, map_mul, map_pow, PowerSeries.constantCoeff_X]
    apply Finset.sum_eq_zero
    intro i _
    have : d - (i : ℕ) ≠ 0 := by have := i.isLt; omega
    rw [zero_pow this, mul_zero]
  split
  · next h =>
    rw [coeff_inv_one_add_pow Fq k _ g hg]
    -- abbreviate e
    set e := (n - ↑d * ↑k).toNat with he_def
    have he : (e : ℤ) = n - ↑d * ↑k := by rw [he_def]; omega
    -- coeff of g ^ y expansion
    have hcoeff : ∀ y : ℕ, (PowerSeries.coeff (R := Fq) e) (g ^ y) =
        ∑ c ∈ (Finset.univ : Finset (Fin d)).piAntidiag y,
          (Nat.multinomial Finset.univ c : Fq) * (∏ i, (θ i) ^ (c i)) *
            (if e = (∑ i : Fin d, (d - (i : ℕ)) * c i) then 1 else 0) := by
      intro y
      rw [hgdef, Finset.sum_pow_eq_sum_piAntidiag, map_sum]
      apply Finset.sum_congr rfl
      intro c hc
      have hprod :
          (∏ i : Fin d,
            ((PowerSeries.C (R:=Fq) (θ i)) * PowerSeries.X ^ (d - (i : ℕ))) ^ (c i))
            = PowerSeries.C (∏ i : Fin d, (θ i) ^ (c i))
              * PowerSeries.X ^ (∑ i : Fin d, (d - (i : ℕ)) * c i) := by
        have step : ∀ i : Fin d,
            ((PowerSeries.C (R:=Fq) (θ i)) * PowerSeries.X ^ (d - (i : ℕ))) ^ (c i)
            = PowerSeries.C ((θ i) ^ (c i)) * PowerSeries.X ^ ((d - (i : ℕ)) * c i) := by
          intro i; rw [mul_pow, ← map_pow, ← pow_mul]
        rw [Finset.prod_congr rfl (fun i _ => step i),
            Finset.prod_mul_distrib, ← map_prod, ← Finset.prod_pow_eq_pow_sum]
      rw [hprod]
      rw [show ((Nat.multinomial Finset.univ c : PowerSeries Fq))
          = PowerSeries.C (Nat.multinomial Finset.univ c : Fq) by
        simp]
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      ring
    -- reindex inner sum: c ↦ c ∘ rev = m
    have hreindex : ∀ y : ℕ,
        (∑ c ∈ (Finset.univ : Finset (Fin d)).piAntidiag y,
          (Nat.multinomial Finset.univ c : Fq) * (∏ i, (θ i) ^ (c i)) *
            (if e = (∑ i : Fin d, (d - (i : ℕ)) * c i) then 1 else 0))
        = ∑ m ∈ (Finset.univ : Finset (Fin d)).piAntidiag y,
          (Nat.multinomial Finset.univ m : Fq) * (∏ i, (θ (Fin.rev i)) ^ (m i)) *
            (if e = weight d m then 1 else 0) := by
      intro y
      apply Finset.sum_nbij' (fun c => c ∘ Fin.rev) (fun m => m ∘ Fin.rev)
      · intro c hc
        rw [Finset.mem_piAntidiag] at hc ⊢
        exact ⟨by rw [← hc.1]; exact Equiv.sum_comp (Fin.revPerm) c, fun i _ => Finset.mem_univ i⟩
      · intro m hm
        rw [Finset.mem_piAntidiag] at hm ⊢
        exact ⟨by rw [← hm.1]; exact Equiv.sum_comp (Fin.revPerm) m, fun i _ => Finset.mem_univ i⟩
      · intro c hc; funext i; simp [Function.comp, Fin.rev_rev]
      · intro m hm; funext i; simp [Function.comp, Fin.rev_rev]
      · intro c hc
        have hmult : Nat.multinomial Finset.univ (c ∘ Fin.rev) = Nat.multinomial Finset.univ c := by
          unfold Nat.multinomial
          have hs : (∑ i, (c ∘ Fin.rev) i) = ∑ i, c i := Equiv.sum_comp (Fin.revPerm) c
          have hp : (∏ i, ((c ∘ Fin.rev) i).factorial) = ∏ i, (c i).factorial :=
            Equiv.prod_comp (Fin.revPerm) (fun i => (c i).factorial)
          rw [hs, hp]
        have hprodθ : (∏ i, (θ (Fin.rev i)) ^ ((c ∘ Fin.rev) i)) = ∏ i, (θ i) ^ (c i) := by
          rw [← Equiv.prod_comp (Fin.revPerm) (fun i => (θ i) ^ (c i))]
          apply Finset.prod_congr rfl
          intro j _; simp [Function.comp, Fin.revPerm_apply]
        have hweight : weight d (c ∘ Fin.rev) = ∑ i : Fin d, (d - (i : ℕ)) * c i := by
          rw [weight, ← Equiv.sum_comp (Fin.revPerm) (fun i => ((i : ℕ) + 1) * (c ∘ Fin.rev) i)]
          apply Finset.sum_congr rfl
          intro j _
          simp only [Function.comp, Fin.revPerm_apply, Fin.rev_rev]
          have hjr : ((Fin.rev j : Fin d) : ℕ) = d - 1 - (j : ℕ) := by rw [Fin.val_rev]; omega
          rw [hjr]
          have hj : (j : ℕ) < d := j.isLt
          congr 1; omega
        rw [hmult, hprodθ, hweight]
    -- apply reindex
    rw [Finset.sum_congr rfl (fun y _ => by rw [hcoeff y, hreindex y])]
    -- define common summand F (RHS)
    set F : (Fin d → ℕ) → Fq := fun m =>
      ((-1) ^ (∑ i, m i) * (Nat.choose (k + (∑ i, m i) - 1) (∑ i, m i) : ℤ)
          * (Nat.multinomial Finset.univ m : ℤ) : Fq) * ∏ i, (θ (Fin.rev i)) ^ (m i) with hF
    -- carrier finset
    set FS := (Fintype.piFinset (fun _ : Fin d => Finset.range (e + 1))).filter
      (fun m => weight d m = e) with hFS
    have hset : {m : Fin d → ℕ | ((d * k : ℕ) + weight d m : ℤ) = n} = ↑FS := by
      ext m
      rw [Finset.mem_coe, hFS, Finset.mem_filter, Fintype.mem_piFinset]
      simp only [Set.mem_setOf_eq, Finset.mem_range]
      constructor
      · intro hm
        have hw : weight d m = e := by
          have hcast : ((d * k : ℕ) : ℤ) + (weight d m : ℤ) = n := by exact_mod_cast hm
          have : (weight d m : ℤ) = (e : ℤ) := by push_cast [he] at hcast ⊢; omega
          exact_mod_cast this
        refine ⟨fun i => ?_, hw⟩
        have hle : m i ≤ weight d m := by
          rw [weight]
          calc m i ≤ ((i : ℕ)+1) * m i := by nlinarith [Nat.zero_le (i : ℕ)]
            _ ≤ ∑ j : Fin d, ((j : ℕ)+1) * m j :=
              Finset.single_le_sum (f := fun j : Fin d => ((j : ℕ)+1) * m j)
                (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      · rintro ⟨_, hw⟩
        have : (weight d m : ℤ) = (e : ℤ) := by exact_mod_cast hw
        push_cast [← he, this]
        omega
    rw [hset, finsum_mem_coe_finset]
    -- LHS → fiberwise
    rw [← Finset.sum_fiberwise_of_maps_to (s := FS) (t := Finset.range (e + 1))
      (g := fun m => ∑ i, m i) (f := F) ?maps]
    · -- termwise
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun m _ =>
        show ((-1) ^ y * (Nat.choose (k + y - 1) y : ℤ) : Fq) *
            ((Nat.multinomial Finset.univ m : Fq) * (∏ i, (θ (Fin.rev i)) ^ (m i)) *
              (if e = weight d m then 1 else 0))
          = if e = weight d m then
              (((-1) ^ y * (Nat.choose (k + y - 1) y : ℤ) : Fq) *
                ((Nat.multinomial Finset.univ m : Fq) * (∏ i, (θ (Fin.rev i)) ^ (m i)))) else 0 by
          split_ifs <;> ring)]
      rw [← Finset.sum_filter]
      apply Finset.sum_nbij' (fun m => m) (fun m => m)
      · intro m hm
        simp only [Finset.mem_filter, Finset.mem_piAntidiag] at hm
        simp only [hFS, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
        obtain ⟨⟨hsum, _⟩, hw⟩ := hm
        refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
        · have hle : m i ≤ weight d m := by
            rw [weight]
            calc m i ≤ ((i : ℕ)+1) * m i := by nlinarith [Nat.zero_le (i : ℕ)]
              _ ≤ ∑ j : Fin d, ((j : ℕ)+1) * m j :=
                Finset.single_le_sum (f := fun j : Fin d => ((j : ℕ)+1) * m j)
                  (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
          omega
        · omega
        · exact hsum
      · intro m hm
        simp only [hFS, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hm
        simp only [Finset.mem_filter, Finset.mem_piAntidiag]
        obtain ⟨⟨_, hw⟩, hsum⟩ := hm
        exact ⟨⟨hsum, fun i _ => Finset.mem_univ i⟩, hw.symm⟩
      · intro m hm; rfl
      · intro m hm; rfl
      · intro m hm
        simp only [Finset.mem_filter, Finset.mem_piAntidiag] at hm
        obtain ⟨⟨hsum, _⟩, hw⟩ := hm
        rw [hF]
        simp only
        rw [hsum]
        push_cast
        ring
    case maps =>
      intro m hm
      rw [hFS, Finset.mem_filter] at hm
      rw [Finset.mem_range]
      show ∑ i, m i < e + 1
      have hw := hm.2
      have : ∑ i, m i ≤ weight d m := by
        rw [weight]
        apply Finset.sum_le_sum
        intro i _; nlinarith [Nat.zero_le (i : ℕ), Nat.zero_le (m i)]
      omega
  · next h =>
    -- LHS = 0; show RHS finsum = 0 because index set is empty
    symm
    apply finsum_mem_eq_zero_of_forall_eq_zero
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    exfalso
    push_cast at hx h
    omega

/-- **L1 (Laurent/multinomial expansion).** The coefficient of `X ^ n` in `Sdk`
equals the `θ`-sum of single-monic-polynomial coefficients, each of which is the
finite tuple-sum of `binom(-k,y)·multinomial(y;m)·∏_i (θ i) ^ {m i}` over tuples `m`
with `d*k + w(m) = n`. -/
theorem Sdk_coeff_as_thetasum (Fq : Type) [Field Fq] [Fintype Fq]
    (d k : ℕ) (n : ℤ) :
    (Sdk Fq d k).coeff n =
      ∑ θ : Fin d → Fq,
        ∑ᶠ m ∈ {m : Fin d → ℕ | ((d * k : ℕ) + weight d m : ℤ) = n},
          ((-1) ^ (∑ i, m i) * (Nat.choose (k + (∑ i, m i) - 1) (∑ i, m i) : ℤ)
              * (Nat.multinomial Finset.univ m : ℤ) : Fq)
            * ∏ i, (θ i) ^ (m i) := by
  -- Push `coeff n` through the finite `θ`-sum, then apply `Sdk_coeff_per_theta` (H5).
  unfold Sdk
  rw [HahnSeries.coeff_sum]
  rw [Finset.sum_congr rfl (fun θ _ => Sdk_coeff_per_theta Fq d k θ n)]
  -- Reindex the finite `θ`-sum by `θ ↦ θ ∘ Fin.rev` (a bijection of `Fin d → Fq`),
  -- which turns `∏ i, (θ (Fin.rev i)) ^ (m i)` into `∏ i, (θ i) ^ (m i)`.
  apply Fintype.sum_bijective (fun θ : Fin d → Fq => θ ∘ Fin.rev)
    (Function.Involutive.bijective (fun θ => by funext i; simp [Function.comp]))
  intro θ
  rfl

/-- **Assembly (b): nonvanishing of `cwit` on the index set.** For `m ∈ T_{d,k-1}`,
`cwit Fq d k m ≠ 0`.  From L3, L4, and L5: membership in `Tindex` supplies both
carry-free conditions, and the global `(-1) ^ d` is a unit. -/
theorem cwit_ne_zero (Fq : Type) [Field Fq] [Fintype Fq]
    (p f d k : ℕ) (hp : p.Prime) (_hf : 1 ≤ f) (_hd : 1 ≤ d) (hk : 0 < k)
    (hchar : CharP Fq p) (_hq : Fintype.card Fq = p ^ f)
    (m : Fin d → ℕ) (hm : Tindex p (Fintype.card Fq) d (k - 1) m) :
    cwit Fq d k m ≠ 0 := by
  obtain ⟨hcf1, hcf2⟩ := (carryfree_combine p (k - 1) d m).mpr hm.2.2
  have h3 : (((-1) ^ (∑ i, m i) * (Nat.choose (k + (∑ i, m i) - 1) (∑ i, m i) : ℤ)) : Fq) ≠ 0 :=
    (negChoose_cast_ne_zero_iff Fq p k hp hchar hk (∑ i, m i)).mpr hcf1
  have h4 : ((Nat.multinomial Finset.univ m : ℤ) : Fq) ≠ 0 :=
    (multinomial_cast_ne_zero_iff Fq p d hp hchar m).mpr hcf2
  unfold cwit
  simp only
  push_cast
  push_cast at h3 h4
  have hsign : ((-1 : Fq)) ^ d ≠ 0 := pow_ne_zero _ (by norm_num)
  have hcombo := mul_ne_zero (mul_ne_zero hsign h3) h4
  intro hzero
  apply hcombo
  rw [← hzero]
  ring

/-- **Assembly (c): the coefficient identity** with the explicit witness `cwit`.
Combines L1 (expansion), L2 (the finite-field power sum collapsing the `θ`-sum to
`(-1) ^ d` exactly when every `m i > 0 ∧ (q - 1) ∣ m i`), and L3/L4/L5 (a term has
nonzero coefficient iff `m ∈ Tindex`), regrouped as the finsum of `cwit` over the
admissible fiber `{m ∈ Tindex | d*k + w(m) = n}`. -/
theorem Sdk_coeff_eq_finsum (Fq : Type) [Field Fq] [Fintype Fq]
    (p f d k : ℕ) (hp : p.Prime) (_hf : 1 ≤ f) (_hd : 1 ≤ d) (hk : 0 < k)
    (hchar : CharP Fq p) (_hq : Fintype.card Fq = p ^ f) (n : ℤ) :
    (Sdk Fq d k).coeff n =
      ∑ᶠ m ∈ {m : Fin d → ℕ | Tindex p (Fintype.card Fq) d (k - 1) m ∧
                ((d * k : ℕ) + weight d m : ℤ) = n}, cwit Fq d k m := by
  -- Start from L1, swap the `θ`-sum past the finsum; L2 collapses
  -- `∑_θ ∏_i (θ i) ^ {m i}` to `(-1) ^ d` exactly when conditions (1),(2) of `Tindex`
  -- hold; condition (3) is automatic since `cwit m = 0` when it fails (L3/L4/L5).
  classical
  rw [Sdk_coeff_as_thetasum Fq d k n]
  -- finite carrier
  set FS := (Fintype.piFinset (fun _ : Fin d => Finset.range ((n - d*k).toNat + 1))).filter
    (fun m => ((d * k : ℕ) + weight d m : ℤ) = n) with hFS
  have hwle : ∀ (m : Fin d → ℕ) (i : Fin d), m i ≤ weight d m := by
    intro m i
    rw [weight]
    calc m i ≤ ((i : ℕ)+1) * m i := by nlinarith [Nat.zero_le (i : ℕ)]
      _ ≤ ∑ j : Fin d, ((j : ℕ)+1) * m j :=
        Finset.single_le_sum (f := fun j : Fin d => ((j : ℕ)+1) * m j)
          (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hset : {m : Fin d → ℕ | ((d * k : ℕ) + weight d m : ℤ) = n} = ↑FS := by
    ext m
    rw [Finset.mem_coe, hFS, Finset.mem_filter, Fintype.mem_piFinset]
    simp only [Set.mem_setOf_eq, Finset.mem_range]
    constructor
    · intro hm
      refine ⟨fun i => ?_, hm⟩
      have hcast : ((d * k : ℕ) : ℤ) + (weight d m : ℤ) = n := by exact_mod_cast hm
      have hle := hwle m i
      have : (weight d m : ℤ) ≤ (n - d*k) := by push_cast at hcast ⊢; omega
      have hwn : weight d m ≤ (n - d*k).toNat := by omega
      omega
    · rintro ⟨_, hm⟩; exact hm
  have hsetT : {m : Fin d → ℕ | Tindex p (Fintype.card Fq) d (k - 1) m ∧
        ((d * k : ℕ) + weight d m : ℤ) = n}
          = ↑(FS.filter (Tindex p (Fintype.card Fq) d (k - 1))) := by
    ext m
    rw [Finset.mem_coe, Finset.mem_filter, hFS, Finset.mem_filter, Fintype.mem_piFinset]
    simp only [Set.mem_setOf_eq, Finset.mem_range]
    constructor
    · rintro ⟨hT, hm⟩
      refine ⟨⟨fun i => ?_, hm⟩, hT⟩
      have hcast : ((d * k : ℕ) : ℤ) + (weight d m : ℤ) = n := by exact_mod_cast hm
      have hle := hwle m i
      have : (weight d m : ℤ) ≤ (n - d*k) := by push_cast at hcast ⊢; omega
      have hwn : weight d m ≤ (n - d*k).toNat := by omega
      omega
    · rintro ⟨⟨_, hm⟩, hT⟩; exact ⟨hT, hm⟩
  rw [hsetT, finsum_mem_coe_finset]
  rw [Finset.sum_congr rfl (fun θ _ => by rw [hset, finsum_mem_coe_finset])]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.mul_sum]
  rw [show (∑ θ : Fin d → Fq, ∏ i, (θ i) ^ (m i)) = ∏ i, (∑ x : Fq, x ^ (m i)) from
    (Fintype.prod_sum fun i j => j ^ m i).symm]
  rw [show (∏ i, (∑ x : Fq, x ^ (m i))) =
      if (∀ i, 0 < m i ∧ (Fintype.card Fq - 1) ∣ m i) then (-1:Fq) ^ d else 0 by
    rw [Finset.prod_congr rfl (fun i _ => finField_pow_sum Fq (m i))]
    by_cases h : ∀ i, 0 < m i ∧ (Fintype.card Fq - 1) ∣ m i
    · rw [if_pos h, Finset.prod_congr rfl (fun i _ => if_pos (h i))]; simp [Finset.prod_const]
    · rw [if_neg h]; push Not at h; obtain ⟨i, hi⟩ := h
      apply Finset.prod_eq_zero (Finset.mem_univ i); rw [if_neg]; intro hc; exact hi hc.1 hc.2]
  set y := ∑ i, m i with hy
  by_cases hcond : ∀ i, 0 < m i ∧ (Fintype.card Fq - 1) ∣ m i
  · rw [if_pos hcond]
    by_cases hT : Tindex p (Fintype.card Fq) d (k - 1) m
    · rw [if_pos hT]; unfold cwit; simp only; push_cast; ring
    · rw [if_neg hT]
      have h1 : ∀ i, 0 < m i := fun i => (hcond i).1
      have h2 : ∀ i, (Fintype.card Fq - 1) ∣ m i := fun i => (hcond i).2
      have hcf : ¬ CarryFree p ((k - 1) :: List.ofFn m) := fun hc => hT ⟨h1, h2, hc⟩
      have hsplit : ¬ (CarryFree p [k-1, y] ∧ CarryFree p (List.ofFn m)) :=
        fun hh => hcf ((carryfree_combine p (k - 1) d m).mp hh)
      have hBzero : (((-1) ^ y * (Nat.choose (k + y - 1) y : ℤ)
          * (Nat.multinomial Finset.univ m : ℤ) : Fq)) = 0 := by
        push_cast
        rw [not_and_or] at hsplit
        rcases hsplit with hb | hmm
        · have hz : ¬ ((((-1) ^ y * (Nat.choose (k + y - 1) y : ℤ)) : Fq) ≠ 0) := by
            rw [negChoose_cast_ne_zero_iff Fq p k hp hchar hk y]; exact hb
          push Not at hz; push_cast at hz; rw [hz, zero_mul]
        · have hz : ¬ (((Nat.multinomial Finset.univ m : ℤ) : Fq) ≠ 0) := by
            rw [multinomial_cast_ne_zero_iff Fq p d hp hchar m]; exact hmm
          push Not at hz; push_cast at hz; rw [hz, mul_zero]
      rw [hBzero, zero_mul]
  · rw [if_neg hcond]
    have hT : ¬ Tindex p (Fintype.card Fq) d (k - 1) m :=
      fun hT => hcond (fun i => ⟨hT.1 i, hT.2.1 i⟩)
    rw [if_neg hT, mul_zero]

/-- **Theorem.**
There exists a family of scalars `c_m ∈ F_q` indexed by `d`-tuples `m`, all
nonzero on the index set `T_{d,k-1}`, such that
  `S_d(k) = t ^ {-dk} ∑_{m ∈ T_{d,k-1}} c_m t ^ {-w(m)}`.

The identity is expressed coefficient-by-coefficient in `F_q((1/t))`: working with
the uniformizer `X = 1/t`, the coefficient of `Xⁿ` (equivalently of `t ^ {-n}`) in
`S_d(k)` equals the sum of `c_m` over the (finite) set of tuples `m ∈ T_{d,k-1}`
with `d*k + w(m) = n`. This faithfully captures that the right-hand side is a
formal sum of monomials `t ^ {-w(m)}` indexed by the tuples (with repetition
allowed): each individual `c_m` is nonzero, while the collected coefficient of a
given power of `t` may vanish. -/
theorem main (Fq : Type) [Field Fq] [Fintype Fq]
    (p f d k : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hd : 1 ≤ d) (hk : 0 < k)
    (hchar : CharP Fq p) (hq : Fintype.card Fq = p ^ f) :
    ∃ c : (Fin d → ℕ) → Fq,
      (∀ m, Tindex p (Fintype.card Fq) d (k - 1) m → c m ≠ 0) ∧
      (∀ n : ℤ, (Sdk Fq d k).coeff n =
        ∑ᶠ m ∈ {m : Fin d → ℕ | Tindex p (Fintype.card Fq) d (k - 1) m ∧
                  ((d * k : ℕ) + weight d m : ℤ) = n}, c m) := by
  -- The witness is the explicit family `cwit Fq d k`; its two required properties
  -- are exactly the assembly lemmas `cwit_ne_zero` and `Sdk_coeff_eq_finsum`.
  refine ⟨cwit Fq d k, ?_, ?_⟩
  · intro m hm
    exact cwit_ne_zero Fq p f d k hp hf hd hk hchar hq m hm
  · intro n
    exact Sdk_coeff_eq_finsum Fq p f d k hp hf hd hk hchar hq n

/-! ## Correctness statements for the definitions

The following auxiliary statements pin down that `monicOf` is the intended
enumeration of the monic polynomials of degree exactly `d`, justifying that
`Sdk` is the power sum `S_d(k) = ∑_{a ∈ A_d ^ +} a ^ {-k}`. -/

/-- The lower-degree part `∑_{i<d} C(θ i) X ^ i` has degree `< d`. -/
theorem monicOf_lower_degree (Fq : Type) [Field Fq] (d : ℕ) (θ : Fin d → Fq) :
    (∑ i : Fin d, C (θ i) * X ^ (i : ℕ)).degree < (d : WithBot ℕ) := by
  apply lt_of_le_of_lt (degree_sum_le Finset.univ _)
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro i _
  apply lt_of_le_of_lt (degree_C_mul_X_pow_le _ _)
  exact_mod_cast i.isLt

/-- `monicOf` always produces a monic polynomial. -/
theorem monicOf_monic (Fq : Type) [Field Fq] (d : ℕ) (θ : Fin d → Fq) :
    (monicOf Fq d θ).Monic := by
  unfold monicOf
  have hlt := monicOf_lower_degree Fq d θ
  apply monic_X_pow_add
  exact hlt

/-- `monicOf` produces a polynomial of degree exactly `d`. -/
theorem monicOf_natDegree (Fq : Type) [Field Fq] (d : ℕ) (θ : Fin d → Fq) :
    (monicOf Fq d θ).natDegree = d := by
  have hm := monicOf_monic Fq d θ
  have hlt := monicOf_lower_degree Fq d θ
  unfold monicOf
  have hdeg : (X ^ d + ∑ i : Fin d, C (θ i) * X ^ (i : ℕ)).degree = (d : WithBot ℕ) := by
    rw [degree_add_eq_left_of_degree_lt]
    · rw [degree_X_pow]
    · rw [degree_X_pow]; exact hlt
  exact natDegree_eq_of_degree_eq_some hdeg

/-- The coefficient of `X ^ i` (for `i < d`) in `monicOf θ` is `θ i`. -/
theorem monicOf_coeff (Fq : Type) [Field Fq] (d : ℕ) (θ : Fin d → Fq)
    (i : Fin d) : (monicOf Fq d θ).coeff (i : ℕ) = θ i := by
  unfold monicOf
  rw [coeff_add, coeff_X_pow]
  rw [if_neg (by exact Nat.ne_of_lt i.isLt)]
  rw [zero_add, finsetSum_coeff]
  rw [Finset.sum_eq_single i]
  · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
  · intro j _ hj
    rw [coeff_C_mul, coeff_X_pow, if_neg, mul_zero]
    exact fun h => hj (Fin.ext h.symm)
  · intro h; exact absurd (Finset.mem_univ i) h

/-- Distinct coefficient tuples give distinct polynomials, so the parameterization
of `A_d ^ +` by `Fin d → Fq` has no repetitions. -/
theorem monicOf_injective (Fq : Type) [Field Fq] (d : ℕ) :
    Function.Injective (monicOf Fq d) := by
  intro θ θ' h
  funext i
  have := monicOf_coeff Fq d θ i
  have h2 := monicOf_coeff Fq d θ' i
  rw [h] at this
  rw [this] at h2
  exact h2

/-- The parameterization is surjective onto `A_d ^ +`: every monic polynomial of
degree exactly `d` arises as `monicOf` of its lower coefficients. -/
theorem monicOf_surjective (Fq : Type) [Field Fq] (d : ℕ) (a : Polynomial Fq)
    (ha : a.Monic) (hdeg : a.natDegree = d) :
    ∃ θ : Fin d → Fq, monicOf Fq d θ = a := by
  refine ⟨fun i => a.coeff (i : ℕ), ?_⟩
  have hsum : a = ∑ i ∈ Finset.range (d + 1), C (a.coeff i) * X ^ i := by
    conv_lhs => rw [a.as_sum_range' (d + 1) (by rw [hdeg]; omega)]
    apply Finset.sum_congr rfl
    intro i _
    rw [C_mul_X_pow_eq_monomial]
  have hcoeff_top : a.coeff d = 1 := by
    have := ha.coeff_natDegree
    rwa [hdeg] at this
  have hfin : (∑ i : Fin d, C (a.coeff (i : ℕ)) * X ^ (i : ℕ))
      = ∑ i ∈ Finset.range d, C (a.coeff i) * X ^ i :=
    Fin.sum_univ_eq_sum_range (fun i => C (a.coeff i) * X ^ i) d
  change X ^ d + ∑ i : Fin d, C (a.coeff (i : ℕ)) * X ^ (i : ℕ) = a
  rw [hfin]
  conv_rhs => rw [hsum, Finset.sum_range_succ, hcoeff_top, map_one, one_mul]
  rw [add_comm]

end ZetaH123.Lem41
