/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import LeanPool.GranvilleMoore.CollapsedCoeff
public import LeanPool.GranvilleMoore.ExplicitForm
public import LeanPool.GranvilleMoore.UnitQuotient
public import Mathlib.NumberTheory.Wilson

-- Adapted for Lean Pool: relocated imports and simplified supporting infrastructure.

/-!
# The master expansion, integrality and the congruences

The end of the elementary route of §3 of Granville's paper. Expanding the numerator of the
explicit form `GranvilleMoore.iteratedFermatQuot_eq_sum_div` along the Frobenius tower turns
`F^{(j)}_k(x)` into a power series in `p^{k+1} g_k(x)` whose coefficients are the collapsed
coefficients `A_j(m)` — the *master expansion*. Each of its terms is `p`-integral, so
`F^{(j)}_k(x)` is an integer; and all but one of them is divisible by `p`, so reducing the
expansion modulo `p` leaves the congruence `j! F^{(j)}_k(x) ≡ x q_p(x)^j`, with one extra
surviving term in the single exceptional case `j = p - 1`, `k = 0`.

## Main results

* `GranvilleMoore.iteratedFermatQuot_eq_mul_sum`: the master expansion
  `F^{(j)}_k(x) = (x^{p^k}/p^{jk + C(j+1,2)}) ∑_{m ≤ e_j} A_j(m) (p^{k+1} g_k(x))^m`.
* `GranvilleMoore.pow_dvd_collapsedCoeff_mul_pow` and
  `GranvilleMoore.pow_succ_dvd_collapsedCoeff_mul_pow`: the `m`-th term is `p`-integral, and
  divisible by `p` off the exceptional patterns.
* `GranvilleMoore.exists_intCast_iteratedFermatQuot`: `F^{(j)}_k(x) ∈ ℤ` for `j ≤ p - 1`.
* `GranvilleMoore.dvd_factorial_mul_sub_mul_pow`:
  `j! F^{(j)}_k(x) ≡ x q_p(x)^j (mod p)` for `j ≤ p - 2`.
* `GranvilleMoore.dvd_factorial_mul_sub_exceptional`:
  `(p-1)! F^{(p-1)}_0(x) ≡ x q_p(x)^{p-1} - x q_p(x) (mod p)`.

## Implementation notes

Everything is proved in `ℤ`. `collapsedCoeff` is `ℚ`-valued, but its defining sum has integer
summands, so `collapsedCoeff_eq_intCast` exhibits it as the cast of an integer, and every
statement that consumes a value of `A_j(m)`, of `g_k(x)`, of `q_p(x)` or of `F^{(j)}_k(x)` takes
the representing integer as an argument together with the hypothesis identifying it — the house
convention of `GranvilleMoore.UnitQuotient`. In particular `numerator_eq_mul_sum`, the
integral core of the master expansion, is stated for an arbitrary `A : ℕ → ℤ` with
`∀ m, collapsedCoeff p j m = (A m : ℚ)`; a consumer that only needs `A` opaquely obtains it
from `⟨_, collapsedCoeff_eq_intCast p j⟩`, and then no cast appears in the rest of its proof.

The integrality of a single term of the master expansion is usually stated as the valuation
inequality `v_p(A_j(m)) + m(k+1) - jk - C(j+1,2) ≥ 0`, strict off `m = j` and
`(m, j, k) = (p, p-1, 0)`. That form is not usable: `padicValRat p 0 = 0`, so it says nothing at
the pairs where `A_j(m)` vanishes — the same defect that forced the algebraic form of the valuation
bound in `GranvilleMoore.CollapsedCoeff`. What is proved here instead is the divisibility
`p^{jk + C(j+1,2)} ∣ A_j(m) p^{m(k+1)}`, respectively with one more factor of `p`, which is what
the numerator of the `m`-th term being a multiple of the common denominator actually means, is
unconditional, and is exactly what `GranvilleMoore.exists_intCast_iteratedFermatQuot` and the two
congruences consume. All the `p`-adic bookkeeping is thereby concentrated in one place,
`pow_dvd_intCollapsedCoeff_mul_pow`, whose only hypothesis is the arithmetic inequality
`D + v_p(m!) ≤ C(j,2) + m(k+1)` on natural numbers; that inequality is where the case analysis on
`m < p`, `m = p`, `m > p` lives, in `padicValNat_factorial_add_le` and
`padicValNat_factorial_add_lt`, and it uses Legendre's bound in the sharp form `(p-1) v_p(m!) < m`.

The congruences are stated as divisibilities between integers rather than as congruences
between rationals, again because the objects are `ℚ`-valued by definition. In both, the power
`p^{jk + C(j+1,2)}` is cancelled by `mul_left_cancel₀` after the surviving term has been
identified, and the unit `(p-1)^j` — which enters because
`GranvilleMoore.CollapsedCoeff` clears denominators by `(p-1)^m` rather than inverting
them — is cancelled at the very end using that `p ∤ p - 1`.

For the exceptional congruence a weaker form allows an unspecified constant `c ≡ 1 (mod p)` on the
`x q_p(x)` term. That constant is `p A_{p-1}(p)/p^{C(p-1,2)}` up to a factor of
`(p-1)! (p-1)^{p-1}`, and `dvd_sub_one_of_mul_eq` computes it to be `≡ 1`, so the clean form with
coefficient exactly `1` is what is stated. The computation needs one coefficient of the rescaled
binomial polynomial beyond the leading one, namely `β_{p,p-1}`; clearing denominators turns `B_p`
into the monic `∏_{s<p}(X - (1 + s(p-1)))`, whose sub-leading coefficient is minus the sum of its
roots, and that sum is divisible by `p` because twice it is `p(2 + (p-1)^2)`.
-/

@[expose] public section

open Finset Polynomial

namespace GranvilleMoore

/-! ### The integer collapsed coefficient -/

/-- The definition of `A_j(m)`, with the inner Frobenius exponent named. -/
private theorem collapsedCoeff_eq_sum_rat (p j m : ℕ) :
    collapsedCoeff p j m = ∑ i ∈ range (j + 1),
      (-1 : ℚ) ^ (j - i) * (cCoeff p j i : ℚ) * ((frobeniusExponent p i).choose m : ℚ) := rfl

/-- `A_j(m)` is the cast of an integer, namely of the same signed sum formed in `ℤ`. -/
private theorem collapsedCoeff_eq_intCast (p j m : ℕ) :
    collapsedCoeff p j m
      = ((∑ i ∈ range (j + 1), (-1 : ℤ) ^ (j - i) * cCoeff p j i *
          ((frobeniusExponent p i).choose m : ℤ) : ℤ) : ℚ) := by
  rw [collapsedCoeff_eq_sum_rat]
  push_cast
  ring

/-! ### Two elementary ingredients -/

/-- The Frobenius exponent is monotone: `e_i ≤ e_j` for `i ≤ j`. -/
private theorem frobeniusExponent_le (p : ℕ) {i j : ℕ} (h : i ≤ j) :
    frobeniusExponent p i ≤ frobeniusExponent p j :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)

/-- `j ≤ e_j`, so the index `j` really does occur in the range of the master expansion. -/
private theorem le_frobeniusExponent {p : ℕ} (hp : 1 ≤ p) (j : ℕ) :
    j ≤ frobeniusExponent p j := by
  rw [frobeniusExponent_eq_sum]
  calc j = ∑ _r ∈ range j, 1 := by simp
    _ ≤ ∑ r ∈ range j, p ^ r := Finset.sum_le_sum fun r _ => Nat.one_le_pow _ _ hp

/-- Newton's binomial theorem about `1`, with the range padded out to any `N ≥ n`:
`(1 + G)^n = ∑_{m ≤ N} C(n,m) G^m`. -/
private theorem one_add_pow_eq_sum_range (G : ℤ) {n N : ℕ} (h : n ≤ N) :
    (1 + G) ^ n = ∑ m ∈ range (N + 1), (n.choose m : ℤ) * G ^ m := by
  have h1 : (1 + G) ^ n = ∑ m ∈ range (n + 1), (n.choose m : ℤ) * G ^ m := by
    rw [add_comm, add_pow]
    exact Finset.sum_congr rfl fun m _ => by rw [one_pow, mul_one, mul_comm]
  rw [h1]
  refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun m _ hm => ?_
  rw [Nat.choose_eq_zero_of_lt (by simp at hm; omega), Nat.cast_zero, zero_mul]

/-! ### The master expansion -/

/-- The numerator of the explicit form, expanded along the Frobenius tower:
`∑_{i ≤ j} (-1)^{j-i} c_{j,i} x^{p^{k+i}} = x^{p^k} ∑_{m ≤ e_j} A_j(m) (p^{k+1} g)^m`,
an identity between integers. The integers representing the values `A_j(m)` are taken as an
argument, as in `GranvilleMoore.fermatUnit_pow_eq_one_add_pow_mul`. -/
private theorem numerator_eq_mul_sum {p : ℕ} (hp : p ≠ 0) {x : ℤ} {k : ℕ} {g : ℤ}
    (hg : unitQuot p x k = (g : ℚ)) (j : ℕ) {A : ℕ → ℤ}
    (hA : ∀ m, collapsedCoeff p j m = (A m : ℚ)) :
    ∑ i ∈ range (j + 1), (-1 : ℤ) ^ (j - i) * cCoeff p j i * x ^ p ^ (k + i)
      = x ^ p ^ k *
        ∑ m ∈ range (frobeniusExponent p j + 1), A m * ((p : ℤ) ^ (k + 1) * g) ^ m := by
  have hAm : ∀ m, A m = ∑ i ∈ range (j + 1), (-1 : ℤ) ^ (j - i) * cCoeff p j i *
      ((frobeniusExponent p i).choose m : ℤ) := fun m => by
    have h := ((collapsedCoeff_eq_intCast p j m).symm.trans (hA m)).symm
    exact_mod_cast h
  simp only [hAm]
  have hu : (x ^ p ^ k) ^ (p - 1) = 1 + (p : ℤ) ^ (k + 1) * g := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact fermatUnit_pow_eq_one_add_pow_mul hp hg
  have hterm : ∀ i ∈ range (j + 1),
      (-1 : ℤ) ^ (j - i) * cCoeff p j i * x ^ p ^ (k + i)
        = ∑ m ∈ range (frobeniusExponent p j + 1),
            x ^ p ^ k * ((-1 : ℤ) ^ (j - i) * cCoeff p j i *
              ((frobeniusExponent p i).choose m : ℤ) * ((p : ℤ) ^ (k + 1) * g) ^ m) := by
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have h1 : (x : ℤ) ^ p ^ (k + i) = (x ^ p ^ k) ^ p ^ i := by rw [← pow_mul, ← pow_add]
    rw [h1, pow_pow_eq_mul_pow_frobeniusExponent hp (x ^ p ^ k) i, hu,
      one_add_pow_eq_sum_range _ (frobeniusExponent_le p hij), Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]

/-- **`lem_master_expansion`**: the master expansion of the iterated Fermat quotient,
```
F^{(j)}_k(x) = (x^{p^k} / p^{jk + C(j+1,2)}) * ∑_{m ≤ e_j} A_j(m) (p^{k+1} g_k(x))^m .
```

Writing `y = x^{p^k}` and `u = y^{p-1} = t_x^{p^k}`, the expansion
`u = 1 + p^{k+1} g_k(x)` of `GranvilleMoore.fermatUnit_pow_eq_one_add_pow_mul` and the
identity `y^{p^i} = y u^{e_i}` of `GranvilleMoore.pow_pow_eq_mul_pow_frobeniusExponent`
turn each power `x^{p^{k+i}}` in the numerator of
`GranvilleMoore.iteratedFermatQuot_eq_sum_div` into `y` times a Newton expansion in
`u - 1`; exchanging the two finite sums leaves the coefficient
`∑_{i ≤ j} (-1)^{j-i} c_{j,i} C(e_i,m)`, which is `A_j(m)`, i.e.
`GranvilleMoore.collapsedCoeff p j m`.

The sum is finite: `C(e_i, m) = 0` once `m > e_i`, and `e_i ≤ e_j` for `i ≤ j`, so
`range (e_j + 1)` already contains every nonvanishing index. -/
theorem iteratedFermatQuot_eq_mul_sum {p : ℕ} (hp : p ≠ 0) {x : ℤ} {j k : ℕ} {g : ℤ}
    (hg : unitQuot p x k = (g : ℚ)) :
    iteratedFermatQuot p j k x
      = (x : ℚ) ^ p ^ k / (p : ℚ) ^ (j * k + Nat.choose (j + 1) 2) *
          ∑ m ∈ range (frobeniusExponent p j + 1),
            collapsedCoeff p j m * ((p : ℚ) ^ (k + 1) * (g : ℚ)) ^ m := by
  have hnum : (∑ i ∈ range (j + 1), (-1 : ℚ) ^ (j - i) * (cCoeff p j i : ℚ) *
        (x : ℚ) ^ p ^ (k + i))
      = (x : ℚ) ^ p ^ k * ∑ m ∈ range (frobeniusExponent p j + 1),
          collapsedCoeff p j m * ((p : ℚ) ^ (k + 1) * (g : ℚ)) ^ m := by
    have h := congrArg (fun z : ℤ => (z : ℚ))
      (numerator_eq_mul_sum hp hg j (collapsedCoeff_eq_intCast p j))
    simp only [collapsedCoeff_eq_sum_rat]
    push_cast at h ⊢
    exact h
  rw [iteratedFermatQuot_eq_sum_div hp, hnum, div_mul_eq_mul_div]

/-! ### The valuation of the factorial -/

/-- The `p`-adic valuation of `m!` is at most `m - p + 1`.

This is Legendre's bound `(p-1) v_p(m!) < m` of
`sub_one_mul_padicValNat_factorial_lt_of_ne_zero`: peeling one copy of `v_p(m!)` off the
left-hand side leaves `(p-2) v_p(m!)`, which is at least `p - 2` as soon as `v_p(m!) ≥ 1`. -/
private theorem padicValNat_factorial_le_succ_sub {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (m : ℕ) : padicValNat p m.factorial ≤ m - p + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (n := m) (by omega)
  set t := padicValNat p m.factorial with ht
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · omega
  have h2 : (p - 2) * 1 ≤ (p - 2) * t := Nat.mul_le_mul_left _ h0
  have h3 : (p - 1) * t = t + (p - 2) * t := by
    rw [show p - 1 = 1 + (p - 2) by omega, Nat.add_mul, one_mul]
  omega

/-- Away from `m = p` the bound of `padicValNat_factorial_le_succ_sub` improves to
`v_p(m!) ≤ m - p`: below `p` the valuation vanishes, and above `p` the same peeling
argument with two copies of `v_p(m!)` gains the extra unit. -/
private theorem padicValNat_factorial_le_sub {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) {m : ℕ}
    (hm : m ≠ p) : padicValNat p m.factorial ≤ m - p := by
  have : Fact p.Prime := ⟨hp⟩
  rcases lt_or_gt_of_ne hm with hlt | hgt
  · rw [padicValNat.eq_zero_of_not_dvd (by rw [hp.dvd_factorial]; omega)]
    omega
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (n := m) (by omega)
  set t := padicValNat p m.factorial with ht
  rcases Nat.lt_or_ge t 2 with h0 | h0
  · interval_cases t <;> omega
  have h2 : (p - 2) * 2 ≤ (p - 2) * t := Nat.mul_le_mul_left _ h0
  have h3 : (p - 1) * t = t + (p - 2) * t := by
    rw [show p - 1 = 1 + (p - 2) by omega, Nat.add_mul, one_mul]
  omega

/-- The exponent inequality behind `pow_dvd_collapsedCoeff_mul_pow`:
`v_p(m!) + j(k+1) ≤ m(k+1)` for `j ≤ p - 1 ` and `j ≤ m`. -/
private theorem padicValNat_factorial_add_le {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    {j m k : ℕ} (hj : j ≤ p - 1) (hjm : j ≤ m) :
    padicValNat p m.factorial + j * (k + 1) ≤ m * (k + 1) := by
  have hsplit : j * (k + 1) + (m - j) * (k + 1) = m * (k + 1) := by
    rw [← Nat.add_mul]; congr 1; omega
  have hle : m - j ≤ (m - j) * (k + 1) := Nat.le_mul_of_pos_right _ (by omega)
  rcases Nat.lt_or_ge m p with hmp | hmp
  · rw [padicValNat.eq_zero_of_not_dvd (by rw [hp.dvd_factorial]; omega)]
    omega
  · have := padicValNat_factorial_le_succ_sub hp hp3 m
    omega

/-- The strict form of `padicValNat_factorial_add_le`, valid off the two exceptional
patterns `m = j` and `(m, j, k) = (p, p - 1, 0)`. -/
private theorem padicValNat_factorial_add_lt {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    {j m k : ℕ} (hj : j ≤ p - 1) (hjm : j < m) (hexc : m ≠ p ∨ j ≠ p - 1 ∨ k ≠ 0) :
    padicValNat p m.factorial + j * (k + 1) < m * (k + 1) := by
  have hsplit : j * (k + 1) + (m - j) * (k + 1) = m * (k + 1) := by
    rw [← Nat.add_mul]; congr 1; omega
  have hle : m - j ≤ (m - j) * (k + 1) := Nat.le_mul_of_pos_right _ (by omega)
  rcases eq_or_ne m p with hmp | hmp
  · have ht : padicValNat p m.factorial ≤ 1 := by
      have := padicValNat_factorial_le_succ_sub hp hp3 m
      omega
    have h2 : 2 ≤ (m - j) * (k + 1) := by
      rcases hexc with h | h | h
      · exact absurd hmp h
      · exact le_trans (by omega) (Nat.mul_le_mul (show 2 ≤ m - j by omega)
          (show 1 ≤ k + 1 by omega))
      · exact le_trans (by omega) (Nat.mul_le_mul (show 1 ≤ m - j by omega)
          (show 2 ≤ k + 1 by omega))
    omega
  · have := padicValNat_factorial_le_sub hp hp3 hmp
    omega

/-! ### Each term of the master expansion is `p`-integral -/

/-- `p - 1` and all its powers are prime to `p`: the units that the clearing of denominators
in `GranvilleMoore.CollapsedCoeff` leaves behind can always be cancelled. -/
private theorem not_dvd_natCast_sub_one_pow {p : ℕ} (hp : p.Prime) (m : ℕ) :
    ¬ (p : ℤ) ∣ ((p : ℤ) - 1) ^ m := by
  have hp' : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hp
  intro hd
  have h1 : (p : ℤ) ∣ 1 := by
    simpa using dvd_sub (dvd_refl ((p : ℤ))) (hp'.dvd_of_dvd_pow hd)
  have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
  have := Int.le_of_dvd zero_lt_one h1
  omega

/-- The `m`-th term of the master expansion, cleared of its denominator: the exponent `D`
that `p^D` divides `A_j(m) p^{m(k+1)}` with is governed by the single inequality
`D + v_p(m!) ≤ C(j,2) + m(k+1)`.

This is `GranvilleMoore.exists_intCast_eq_factorial_mul_pow_mul_collapsedCoeff` with `m!`
split as `p^{v_p(m!)}` times a unit: cancelling that power of `p` and then the units `m!/p^t`
and `(p-1)^m`, both prime to `p`, leaves the stated divisibility. -/
private theorem pow_dvd_intCollapsedCoeff_mul_pow {p : ℕ} (hp : p.Prime) {j m k D : ℕ}
    (hD : D + padicValNat p m.factorial ≤ j.choose 2 + m * (k + 1))
    {A : ℤ} (hA : collapsedCoeff p j m = (A : ℚ)) :
    (p : ℤ) ^ D ∣ A * (p : ℤ) ^ (m * (k + 1)) := by
  have hfact : Fact p.Prime := ⟨hp⟩
  have hp' : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hp
  have hpz : ((p : ℤ)) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  set t := padicValNat p m.factorial with ht
  obtain ⟨s, hs⟩ := pow_padicValNat_dvd (p := p) (n := m.factorial)
  have hps : ¬ p ∣ s := by
    intro hd
    obtain ⟨c, hc⟩ := hd
    have hdvd : p ^ (t + 1) ∣ m.factorial := ⟨c, by rw [hs, hc, pow_succ]; ring⟩
    have := (padicValNat_dvd_iff_le m.factorial_ne_zero).mp hdvd
    omega
  have hsZ : ((m.factorial : ℕ) : ℤ) = (p : ℤ) ^ t * (s : ℤ) := by rw [hs]; push_cast; ring
  obtain ⟨a, ha⟩ := exists_intCast_eq_factorial_mul_pow_mul_collapsedCoeff hp.two_le j m
  rw [hA] at ha
  have haZ : (m.factorial : ℤ) * ((p : ℤ) - 1) ^ m * A = (p : ℤ) ^ j.choose 2 * a := by
    exact_mod_cast ha
  have key : (p : ℤ) ^ t * ((p : ℤ) ^ D)
      ∣ (p : ℤ) ^ t * ((s : ℤ) * (((p : ℤ) - 1) ^ m * (A * (p : ℤ) ^ (m * (k + 1))))) := by
    rw [show (p : ℤ) ^ t * ((s : ℤ) * (((p : ℤ) - 1) ^ m * (A * (p : ℤ) ^ (m * (k + 1)))))
        = ((m.factorial : ℤ) * ((p : ℤ) - 1) ^ m * A) * (p : ℤ) ^ (m * (k + 1)) by
      rw [hsZ]; ring, haZ, ← pow_add,
      show (p : ℤ) ^ j.choose 2 * a * (p : ℤ) ^ (m * (k + 1))
        = (p : ℤ) ^ (j.choose 2 + m * (k + 1)) * a by rw [pow_add]; ring]
    exact (pow_dvd_pow ((p : ℤ)) (by omega : t + D ≤ j.choose 2 + m * (k + 1))).mul_right a
  have h1 : (p : ℤ) ^ D ∣ (s : ℤ) * (((p : ℤ) - 1) ^ m * (A * (p : ℤ) ^ (m * (k + 1)))) :=
    (mul_dvd_mul_iff_left (pow_ne_zero t hpz)).mp key
  exact hp'.pow_dvd_of_dvd_mul_left D (not_dvd_natCast_sub_one_pow hp m)
    (hp'.pow_dvd_of_dvd_mul_left D (by rwa [Int.natCast_dvd_natCast]) h1)

/-- The exponent identity `jk + C(j+1,2) = j(k+1) + C(j,2)`, which is `C(j+1,2) = C(j,2) + j`
with the `j` moved into the first summand. -/
private theorem exponent_eq (j k : ℕ) :
    j * k + Nat.choose (j + 1) 2 = j * (k + 1) + Nat.choose j 2 := by
  rw [Nat.choose_succ_succ j 1, Nat.choose_one_right]
  ring

/-- **`lem_master_term_integral`**, integrality: `p^{jk + C(j+1,2)}` divides
`A_j(m) p^{m(k+1)}` for `j ≤ p - 1` and `m ≥ j`, so the `m`-th term of the master expansion
is `p`-integral.

The usual statement is the valuation inequality `v_p(A_j(m)) + m(k+1) - jk - C(j+1,2) ≥ 0`; this is
its algebraic form, in which the numerator of the term is exhibited as a multiple of the
denominator `p^{jk + C(j+1,2)}` of `GranvilleMoore.iteratedFermatQuot_eq_sum_div`. It reduces, via
`GranvilleMoore.exists_intCast_eq_factorial_mul_pow_mul_collapsedCoeff`, to the arithmetic
`v_p(m!) + j(k+1) ≤ m(k+1)` of `padicValNat_factorial_add_le`. -/
theorem pow_dvd_collapsedCoeff_mul_pow {p : ℕ} (hp : p.Prime) (hodd : Odd p) {j m k : ℕ}
    (hj : j ≤ p - 1) (hjm : j ≤ m) {A : ℤ} (hA : collapsedCoeff p j m = (A : ℚ)) :
    (p : ℤ) ^ (j * k + Nat.choose (j + 1) 2) ∣ A * (p : ℤ) ^ (m * (k + 1)) := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    have : p % 2 = 1 := Nat.odd_iff.mp hodd
    omega
  refine pow_dvd_intCollapsedCoeff_mul_pow hp ?_ hA
  have h := padicValNat_factorial_add_le hp hp3 (k := k) hj hjm
  rw [exponent_eq]
  omega

/-- **`lem_master_term_integral`**, strict positivity: off the exceptional patterns `m = j`
and `(m, j, k) = (p, p - 1, 0)` the divisibility of
`GranvilleMoore.pow_dvd_collapsedCoeff_mul_pow` holds with one more factor of `p`, so the
`m`-th term of the master expansion is divisible by `p`.

This is the second half of that lemma, and it is what makes only finitely many terms survive modulo
`p` in `GranvilleMoore.dvd_factorial_mul_sub_mul_pow` and
`GranvilleMoore.dvd_factorial_mul_sub_exceptional`. -/
theorem pow_succ_dvd_collapsedCoeff_mul_pow {p : ℕ} (hp : p.Prime) (hodd : Odd p) {j m k : ℕ}
    (hj : j ≤ p - 1) (hjm : j < m) (hexc : m ≠ p ∨ j ≠ p - 1 ∨ k ≠ 0) {A : ℤ}
    (hA : collapsedCoeff p j m = (A : ℚ)) :
    (p : ℤ) ^ (j * k + Nat.choose (j + 1) 2 + 1) ∣ A * (p : ℤ) ^ (m * (k + 1)) := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    have : p % 2 = 1 := Nat.odd_iff.mp hodd
    omega
  refine pow_dvd_intCollapsedCoeff_mul_pow hp ?_ hA
  have h := padicValNat_factorial_add_lt hp hp3 (k := k) hj hjm hexc
  rw [exponent_eq]
  omega

/-! ### Integrality -/

/-- The numerator of the explicit form is divisible by its denominator: this is the whole
content of `GranvilleMoore.exists_intCast_iteratedFermatQuot`, in `ℤ`. -/
private theorem pow_dvd_numerator {p : ℕ} (hp : p.Prime) (hodd : Odd p) {x : ℤ}
    (hx : ¬ (p : ℤ) ∣ x) {j : ℕ} (hj : j ≤ p - 1) (k : ℕ) :
    (p : ℤ) ^ (j * k + Nat.choose (j + 1) 2)
      ∣ ∑ i ∈ range (j + 1), (-1 : ℤ) ^ (j - i) * cCoeff p j i * x ^ p ^ (k + i) := by
  obtain ⟨g, hg⟩ := unitQuot_eq_intCast hp hodd hx k
  rw [numerator_eq_mul_sum hp.ne_zero hg j (collapsedCoeff_eq_intCast p j)]
  refine Dvd.dvd.mul_left (Finset.dvd_sum fun m _ => ?_) _
  rcases lt_or_ge m j with hmj | hmj
  · rw [show (∑ i ∈ range (j + 1), (-1 : ℤ) ^ (j - i) * cCoeff p j i *
        ((frobeniusExponent p i).choose m : ℤ)) = 0 by
      have h := collapsedCoeff_eq_zero (p := p) hp.two_le hmj
      rw [collapsedCoeff_eq_intCast] at h
      exact_mod_cast h, zero_mul]
    exact dvd_zero _
  · have h := pow_dvd_collapsedCoeff_mul_pow (k := k) hp hodd hj hmj
      (collapsedCoeff_eq_intCast p j m)
    rw [show (∑ i ∈ range (j + 1), (-1 : ℤ) ^ (j - i) * cCoeff p j i *
          ((frobeniusExponent p i).choose m : ℤ)) * ((p : ℤ) ^ (k + 1) * g) ^ m
        = ((∑ i ∈ range (j + 1), (-1 : ℤ) ^ (j - i) * cCoeff p j i *
            ((frobeniusExponent p i).choose m : ℤ)) * (p : ℤ) ^ (m * (k + 1))) * g ^ m by
      rw [mul_pow, ← pow_mul, mul_comm (k + 1) m]; ring]
    exact h.mul_right _

/-- **`thm_fermat_integral`**: for an odd prime `p` with `p ∤ x` and `0 ≤ j ≤ p - 1`, the
iterated Fermat quotient `F^{(j)}_k(x)` is an integer, for every `k`.

Integrality is phrased as the existence of an integer whose cast is the value, matching
`GranvilleMoore.unitQuot_eq_intCast` and `GranvilleMoore.fermatQuotient_eq_intCast`.

The proof stays in `ℤ`. The explicit form
`GranvilleMoore.iteratedFermatQuot_eq_sum_div` exhibits `F^{(j)}_k(x)` as an integer
numerator over `p^{jk + C(j+1,2)}`, so it is enough to divide the numerator by that power of
`p`; the master expansion rewrites the numerator as a sum of terms each of which
`GranvilleMoore.pow_dvd_collapsedCoeff_mul_pow` shows to be divisible by it. -/
theorem exists_intCast_iteratedFermatQuot {p : ℕ} (hp : p.Prime) (hodd : Odd p) {x : ℤ}
    (hx : ¬ (p : ℤ) ∣ x) {j : ℕ} (hj : j ≤ p - 1) (k : ℕ) :
    ∃ z : ℤ, iteratedFermatQuot p j k x = (z : ℚ) := by
  obtain ⟨w, hw⟩ := pow_dvd_numerator hp hodd hx hj k
  refine ⟨w, ?_⟩
  have hpne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hnum : (∑ i ∈ range (j + 1), (-1 : ℚ) ^ (j - i) * (cCoeff p j i : ℚ) *
      (x : ℚ) ^ p ^ (k + i)) = (p : ℚ) ^ (j * k + Nat.choose (j + 1) 2) * (w : ℚ) := by
    have h := congrArg (fun v : ℤ => (v : ℚ)) hw
    push_cast at h
    exact h
  rw [iteratedFermatQuot_eq_sum_div hp.ne_zero, hnum,
    mul_div_cancel_left₀ _ (pow_ne_zero _ hpne)]

/-! ### The congruence -/

/-- The explicit form read backwards, once the value is known to be the integer `z`: the
numerator is `p^{jk + C(j+1,2)} z`. -/
private theorem numerator_eq_pow_mul {p : ℕ} (hp : p.Prime) {x : ℤ} {j k : ℕ} {z : ℤ}
    (hz : iteratedFermatQuot p j k x = (z : ℚ)) :
    ∑ i ∈ range (j + 1), (-1 : ℤ) ^ (j - i) * cCoeff p j i * x ^ p ^ (k + i)
      = (p : ℤ) ^ (j * k + Nat.choose (j + 1) 2) * z := by
  have hpne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  rw [iteratedFermatQuot_eq_sum_div hp.ne_zero, div_eq_iff (pow_ne_zero _ hpne)] at hz
  refine Int.cast_injective (α := ℚ) ?_
  push_cast
  linear_combination hz

/-- Every index of the master expansion other than `m = j` contributes a multiple of
`p^{jk + C(j+1,2) + 1}`, provided the exceptional pattern is excluded: below `j` the
coefficient `A_j(m)` vanishes, and above it
`GranvilleMoore.pow_succ_dvd_collapsedCoeff_mul_pow` applies. -/
private theorem pow_succ_dvd_sum_erase {p : ℕ} (hp : p.Prime) (hodd : Odd p) {j k : ℕ}
    (hj : j ≤ p - 1) (hne : j ≠ p - 1 ∨ k ≠ 0) {g : ℤ} {A : ℕ → ℤ}
    (hA : ∀ m, collapsedCoeff p j m = (A m : ℚ)) :
    (p : ℤ) ^ (j * k + Nat.choose (j + 1) 2 + 1)
      ∣ ∑ m ∈ (range (frobeniusExponent p j + 1)).erase j,
          A m * ((p : ℤ) ^ (k + 1) * g) ^ m := by
  refine Finset.dvd_sum fun m hm => ?_
  have hmne : m ≠ j := Finset.ne_of_mem_erase hm
  rw [show A m * ((p : ℤ) ^ (k + 1) * g) ^ m = (A m * (p : ℤ) ^ (m * (k + 1))) * g ^ m by
    rw [mul_pow, ← pow_mul, mul_comm (k + 1) m]; ring]
  rcases lt_or_gt_of_ne hmne with hmj | hmj
  · have h0 : ((A m : ℤ) : ℚ) = 0 := by
      rw [← hA m]; exact collapsedCoeff_eq_zero hp.two_le hmj
    rw [show A m = 0 from by exact_mod_cast h0, zero_mul, zero_mul]
    exact dvd_zero _
  · exact (pow_succ_dvd_collapsedCoeff_mul_pow hp hodd hj hmj
      (Or.inr hne) (hA m)).mul_right _

/-- **`thm_fermat_congruence`**: for an odd prime `p` with `p ∤ x` and `0 ≤ j ≤ p - 2`,
```
j! F^{(j)}_k(x) ≡ x q_p(x)^j  (mod p) ,
```
stated as divisibility between the integers `z` representing `F^{(j)}_k(x)` (which exists by
`GranvilleMoore.exists_intCast_iteratedFermatQuot`) and `q` representing `q_p(x)`.

Only the term `m = j` of the master expansion survives modulo `p`: every other one is
divisible by `p` by `GranvilleMoore.pow_succ_dvd_collapsedCoeff_mul_pow`, whose exceptional
pattern needs `j = p - 1` and is excluded by `j ≤ p - 2`. The surviving term is
`x^{p^k} (A_j(j)/p^{C(j,2)}) g_k(x)^j`, and
`GranvilleMoore.exists_int_factorial_mul_pow_mul_collapsedCoeff_self` supplies
`j! (p-1)^j A_j(j) = p^{C(j,2)} ((p-1)^j + p a)`. Reducing modulo `p` then uses
`x^{p^k} ≡ x` (Fermat), `g_k(x) ≡ q_p(x)`
(`GranvilleMoore.dvd_unitQuot_sub_fermatQuotient`) and finally cancels the unit `(p-1)^j`. -/
theorem dvd_factorial_mul_sub_mul_pow {p : ℕ} (hp : p.Prime) (hodd : Odd p) {x : ℤ}
    (hx : ¬ (p : ℤ) ∣ x) {j : ℕ} (hj : j ≤ p - 2) (k : ℕ) {z q : ℤ}
    (hz : iteratedFermatQuot p j k x = (z : ℚ)) (hq : fermatQuotient p x = (q : ℚ)) :
    (p : ℤ) ∣ (j.factorial : ℤ) * z - x * q ^ j := by
  have hfact : Fact p.Prime := ⟨hp⟩
  have hp' : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hp
  have hpz : ((p : ℤ)) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    have : p % 2 = 1 := Nat.odd_iff.mp hodd
    omega
  obtain ⟨g, hg⟩ := unitQuot_eq_intCast hp hodd hx k
  have hgq := dvd_unitQuot_sub_fermatQuotient hp hodd hg hq
  obtain ⟨A, hA⟩ : ∃ A : ℕ → ℤ, ∀ m, collapsedCoeff p j m = (A m : ℚ) :=
    ⟨_, collapsedCoeff_eq_intCast p j⟩
  obtain ⟨R, hR⟩ := pow_succ_dvd_sum_erase hp hodd (by omega) (Or.inl (by omega)) (g := g) hA
  have hnum := (numerator_eq_pow_mul hp hz).symm.trans
    (numerator_eq_mul_sum hp.ne_zero hg j hA)
  rw [← Finset.add_sum_erase _ (fun m => A m * ((p : ℤ) ^ (k + 1) * g) ^ m)
      (mem_range.mpr (Nat.lt_succ_of_le (le_frobeniusExponent (by omega) j))), hR] at hnum
  obtain ⟨a, ha⟩ := exists_int_factorial_mul_pow_mul_collapsedCoeff_self hp.two_le j
  rw [hA j] at ha
  have hWA : (j.factorial : ℤ) * ((p : ℤ) - 1) ^ j * A j
      = (p : ℤ) ^ Nat.choose j 2 * (((p : ℤ) - 1) ^ j + (p : ℤ) * a) := by
    exact_mod_cast ha
  have hMC : (p : ℤ) ^ (j * k + Nat.choose (j + 1) 2)
      = (p : ℤ) ^ (j * (k + 1)) * (p : ℤ) ^ Nat.choose j 2 := by
    rw [exponent_eq, pow_add]
  have hGj : ((p : ℤ) ^ (k + 1) * g) ^ j = (p : ℤ) ^ (j * (k + 1)) * g ^ j := by
    rw [mul_pow, ← pow_mul, mul_comm (k + 1) j]
  rw [hMC, hGj, pow_succ, hMC] at hnum
  have hmid : (p : ℤ) ∣ (j.factorial : ℤ) * ((p : ℤ) - 1) ^ j * z
      - x ^ p ^ k * (((p : ℤ) - 1) ^ j + (p : ℤ) * a) * g ^ j := by
    refine ⟨x ^ p ^ k * ((j.factorial : ℤ) * ((p : ℤ) - 1) ^ j) * R, ?_⟩
    refine mul_left_cancel₀ (mul_ne_zero (pow_ne_zero (j * (k + 1)) hpz)
      (pow_ne_zero (Nat.choose j 2) hpz)) ?_
    linear_combination ((j.factorial : ℤ) * ((p : ℤ) - 1) ^ j) * hnum
      + (x ^ p ^ k * (p : ℤ) ^ (j * (k + 1)) * g ^ j) * hWA
  have hZ : (p : ℤ) ∣ x ^ p ^ k * (((p : ℤ) - 1) ^ j + (p : ℤ) * a) * g ^ j
      - ((p : ℤ) - 1) ^ j * (x * q ^ j) := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_
    have hgq' : ((g : ℤ) : ZMod p) = ((q : ℤ) : ZMod p) := by
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (g - q) p).mpr hgq
      push_cast at h
      linear_combination h
    push_cast
    rw [ZMod.natCast_self, hgq', ZMod.pow_card_pow]
    ring
  have hfin : (p : ℤ) ∣ ((p : ℤ) - 1) ^ j * ((j.factorial : ℤ) * z - x * q ^ j) := by
    have h := dvd_add hmid hZ
    rwa [show ((j.factorial : ℤ) * ((p : ℤ) - 1) ^ j * z
          - x ^ p ^ k * (((p : ℤ) - 1) ^ j + (p : ℤ) * a) * g ^ j)
        + (x ^ p ^ k * (((p : ℤ) - 1) ^ j + (p : ℤ) * a) * g ^ j
          - ((p : ℤ) - 1) ^ j * (x * q ^ j))
        = ((p : ℤ) - 1) ^ j * ((j.factorial : ℤ) * z - x * q ^ j) by ring] at h
  rcases hp'.dvd_mul.mp hfin with h | h
  · exact absurd h (not_dvd_natCast_sub_one_pow hp j)
  · exact h

/-! ### The exceptional congruence -/

/-- The rescaled binomial polynomial with all denominators cleared, written as a product of
monic linear factors: `m! (p-1)^m B_m = ∏_{s<m} (X - (1 + s(p-1)))`.

This is `GranvilleMoore.C_mul_binomPoly_eq_prod` with each factor `X - 1 - s(p-1)` folded
into the shape `X - C c` that Mathlib's symmetric-function API expects. -/
private theorem clearedBinomPoly_eq {p : ℕ} (hp : p ≠ 1) (m : ℕ) :
    C ((m.factorial : ℚ) * ((p : ℚ) - 1) ^ m) * binomPoly p m
      = ∏ s ∈ range m, (X - C (1 + (s : ℚ) * ((p : ℚ) - 1))) := by
  rw [C_mul_binomPoly_eq_prod hp m]
  exact Finset.prod_congr rfl fun s _ => by rw [map_add, map_one]; ring

private theorem natDegree_clearedBinomPoly (p m : ℕ) :
    (∏ s ∈ range m, (X - C (1 + (s : ℚ) * ((p : ℚ) - 1)))).natDegree = m := by
  rw [natDegree_prod_of_monic _ _ fun _s _ => monic_X_sub_C _]
  simp only [natDegree_X_sub_C, Finset.sum_const, card_range, smul_eq_mul, mul_one]

/-- The top coefficient of the cleared binomial polynomial is `1`: it is monic of degree
`m`. Equivalently `m! (p-1)^m β_{m,m} = 1`. -/
private theorem coeff_clearedBinomPoly_self (p m : ℕ) :
    (∏ s ∈ range m, (X - C (1 + (s : ℚ) * ((p : ℚ) - 1)))).coeff m = 1 := by
  have h := (monic_prod_of_monic (range m)
    (fun s => X - C (1 + (s : ℚ) * ((p : ℚ) - 1))) fun _s _ => monic_X_sub_C _).coeff_natDegree
  rwa [natDegree_clearedBinomPoly] at h

/-- The sub-leading coefficient of the cleared binomial polynomial is minus the sum of its
roots, `-∑_{s<m} (1 + s(p-1))`. This is the one extra coefficient that the exceptional
congruence needs, and it is `Polynomial.prod_X_sub_C_nextCoeff`. -/
private theorem coeff_clearedBinomPoly_pred {p m : ℕ} (hm : 0 < m) :
    (∏ s ∈ range m, (X - C (1 + (s : ℚ) * ((p : ℚ) - 1)))).coeff (m - 1)
      = -∑ s ∈ range m, (1 + (s : ℚ) * ((p : ℚ) - 1)) := by
  have h := Polynomial.prod_X_sub_C_nextCoeff (s := range m)
    (fun s : ℕ => (1 + (s : ℚ) * ((p : ℚ) - 1)))
  rwa [Polynomial.nextCoeff_of_natDegree_pos (by rw [natDegree_clearedBinomPoly]; omega),
    natDegree_clearedBinomPoly] at h

/-- The closed form of the one collapsed coefficient the exceptional congruence needs,
`A_{p-1}(p)`:
```
p! (p-1)^p A_{p-1}(p)
  = p^{C(p-1,2)} ( -(∑_{s<p}(1 + s(p-1))) ∏_{r<p-1}(p^{p-1-r} - 1) + ∏_{r<p-1}(p^{p-r} - 1) ) .
```

In the closed form `GranvilleMoore.collapsedCoeff_eq_sum` at `(j, m) = (p-1, p)` only the two
indices `n = p - 1` and `n = p` survive, the rest vanishing by
`GranvilleMoore.prod_pow_sub_pow_eq_zero`; the two coefficients `p! (p-1)^p β_{p,n}` are the
top and the sub-leading coefficient of the cleared binomial polynomial, and each of the two
remaining products contributes the same factor `p^{C(p-1,2)}`. -/
private theorem factorial_mul_pow_mul_collapsedCoeff_exceptional {p : ℕ} (hp : p.Prime)
    (hp3 : 3 ≤ p) :
    (p.factorial : ℚ) * ((p : ℚ) - 1) ^ p * collapsedCoeff p (p - 1) p
      = (p : ℚ) ^ Nat.choose (p - 1) 2 *
        ((-∑ s ∈ range p, (1 + (s : ℚ) * ((p : ℚ) - 1))) *
            (∏ r ∈ range (p - 1), ((p : ℚ) ^ (p - 1 - r) - 1))
          + ∏ r ∈ range (p - 1), ((p : ℚ) ^ (p - r) - 1)) := by
  have hcoeff : ∀ n, (p.factorial : ℚ) * ((p : ℚ) - 1) ^ p * binomPolyCoeff p p n
      = (∏ s ∈ range p, (X - C (1 + (s : ℚ) * ((p : ℚ) - 1)))).coeff n := fun n => by
    rw [binomPolyCoeff, ← Polynomial.coeff_C_mul, clearedBinomPoly_eq (by omega)]
  have hstep : ∀ n ∈ range (p + 1),
      (p.factorial : ℚ) * ((p : ℚ) - 1) ^ p *
        (binomPolyCoeff p p n * ∏ r ∈ range (p - 1), ((p : ℚ) ^ n - (p : ℚ) ^ r))
      = (∏ s ∈ range p, (X - C (1 + (s : ℚ) * ((p : ℚ) - 1)))).coeff n
          * ∏ r ∈ range (p - 1), ((p : ℚ) ^ n - (p : ℚ) ^ r) := fun n _ => by
    rw [← hcoeff n]; ring
  rw [collapsedCoeff_eq_sum hp.two_le, Finset.mul_sum, Finset.sum_congr rfl hstep,
    show p + 1 = (p - 1) + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_eq_zero (fun n hn => by
      rw [prod_pow_sub_pow_rat_eq_zero (mem_range.mp hn), mul_zero]),
    show p - 1 + 1 = p by omega, zero_add,
    coeff_clearedBinomPoly_pred (show 0 < p by omega), coeff_clearedBinomPoly_self,
    prod_pow_sub_pow_rat_eq_pow_mul (show p - 1 ≤ p - 1 from le_refl _),
    prod_pow_sub_pow_rat_eq_pow_mul (show p - 1 ≤ p by omega)]
  ring

/-- The normalisation constant of the exceptional congruence is `≡ 1 (mod p)`: if
`p A_{p-1}(p) = p^{C(p-1,2)} b` then `b ≡ 1 (mod p)`.

This is what makes the coefficient of `x q_p(x)` in
`GranvilleMoore.dvd_factorial_mul_sub_exceptional` exactly `1`. In the closed form of
`factorial_mul_pow_mul_collapsedCoeff_exceptional` the sub-leading coefficient
`-∑_{s<p}(1 + s(p-1))` is divisible by `p` — twice it is `p (2 + (p-1)^2)` — while each factor
`p^e - 1` of the two remaining products is `≡ -1`, so each product is `≡ (-1)^{p-1} = 1`.
Together with Wilson's theorem `(p-1)! ≡ -1` and `(p-1)^p ≡ -1` this leaves `b ≡ 1`. -/
private theorem dvd_sub_one_of_mul_eq {p : ℕ} (hp : p.Prime) (hodd : Odd p) {A' b : ℤ}
    (hA' : collapsedCoeff p (p - 1) p = (A' : ℚ))
    (hb : (p : ℤ) * A' = (p : ℤ) ^ Nat.choose (p - 1) 2 * b) :
    (p : ℤ) ∣ b - 1 := by
  have hfact : Fact p.Prime := ⟨hp⟩
  have hp' : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hp
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    have : p % 2 = 1 := Nat.odd_iff.mp hodd
    omega
  have hpne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hfacp : (p.factorial : ℚ) = (p : ℚ) * (((p - 1).factorial : ℕ) : ℚ) := by
    rw [← Nat.mul_factorial_pred (show p ≠ 0 by omega)]
    push_cast
    ring
  have hQ := factorial_mul_pow_mul_collapsedCoeff_exceptional hp hp3
  rw [hA', hfacp] at hQ
  have hbQ : (p : ℚ) * (A' : ℚ) = (p : ℚ) ^ Nat.choose (p - 1) 2 * (b : ℚ) := by
    exact_mod_cast congrArg (fun w : ℤ => (w : ℚ)) hb
  have hkey : (((p - 1).factorial : ℕ) : ℚ) * ((p : ℚ) - 1) ^ p * (b : ℚ)
      = (-∑ s ∈ range p, (1 + (s : ℚ) * ((p : ℚ) - 1))) *
            (∏ r ∈ range (p - 1), ((p : ℚ) ^ (p - 1 - r) - 1))
          + ∏ r ∈ range (p - 1), ((p : ℚ) ^ (p - r) - 1) := by
    refine mul_left_cancel₀ (pow_ne_zero (Nat.choose (p - 1) 2) hpne) ?_
    linear_combination hQ - ((((p - 1).factorial : ℕ) : ℚ) * ((p : ℚ) - 1) ^ p) * hbQ
  have hkeyZ : (((p - 1).factorial : ℕ) : ℤ) * ((p : ℤ) - 1) ^ p * b
      = (-∑ s ∈ range p, (1 + (s : ℤ) * ((p : ℤ) - 1))) *
            (∏ r ∈ range (p - 1), ((p : ℤ) ^ (p - 1 - r) - 1))
          + ∏ r ∈ range (p - 1), ((p : ℤ) ^ (p - r) - 1) := by
    exact_mod_cast hkey
  have hSZ : (p : ℤ) ∣ ∑ s ∈ range p, (1 + (s : ℤ) * ((p : ℤ) - 1)) := by
    have hsplit : ∑ s ∈ range p, (1 + (s : ℤ) * ((p : ℤ) - 1))
        = (p : ℤ) + ((p : ℤ) - 1) * ∑ s ∈ range p, (s : ℤ) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, card_range, Finset.mul_sum]
      simp only [nsmul_eq_mul, mul_one]
      exact congrArg _ (Finset.sum_congr rfl fun s _ => by ring)
    have hid : (∑ i ∈ range p, (i : ℤ)) * 2 = (p : ℤ) * ((p : ℤ) - 1) := by
      have h2 : ((∑ i ∈ range p, i : ℕ) : ℤ) * 2 = ((p * (p - 1) : ℕ) : ℤ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (Finset.sum_range_id_mul_two p)
      push_cast [Nat.cast_sub (show 1 ≤ p by omega)] at h2
      linarith [h2]
    have h2S : (2 : ℤ) * ∑ s ∈ range p, (1 + (s : ℤ) * ((p : ℤ) - 1))
        = (p : ℤ) * (2 + ((p : ℤ) - 1) * ((p : ℤ) - 1)) := by
      rw [hsplit]
      linear_combination ((p : ℤ) - 1) * hid
    refine (hp'.dvd_mul.mp ⟨2 + ((p : ℤ) - 1) * ((p : ℤ) - 1), h2S⟩).resolve_left ?_
    intro hd
    have h3 : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
    have := Int.le_of_dvd (by norm_num) hd
    omega
  have hR1 : ((∏ r ∈ range (p - 1), ((p : ℤ) ^ (p - 1 - r) - 1) : ℤ) : ZMod p) = 1 := by
    push_cast
    rw [Finset.prod_congr rfl (fun r hr => show ((p : ZMod p)) ^ (p - 1 - r) - 1 = -1 by
      have hr' := mem_range.mp hr
      rw [ZMod.natCast_self, zero_pow (by omega : p - 1 - r ≠ 0)]; ring),
      Finset.prod_const, card_range]
    exact Even.neg_one_pow (Nat.Odd.sub_odd hodd odd_one)
  have hR2 : ((∏ r ∈ range (p - 1), ((p : ℤ) ^ (p - r) - 1) : ℤ) : ZMod p) = 1 := by
    push_cast
    rw [Finset.prod_congr rfl (fun r hr => show ((p : ZMod p)) ^ (p - r) - 1 = -1 by
      have hr' := mem_range.mp hr
      rw [ZMod.natCast_self, zero_pow (by omega : p - r ≠ 0)]; ring),
      Finset.prod_const, card_range]
    exact Even.neg_one_pow (Nat.Odd.sub_odd hodd odd_one)
  have hS0 : ((∑ s ∈ range p, (1 + (s : ℤ) * ((p : ℤ) - 1)) : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hSZ
  have hZ := congrArg (fun w : ℤ => (w : ZMod p)) hkeyZ
  simp only [Int.cast_add, Int.cast_mul, Int.cast_neg, Int.cast_sub, Int.cast_pow,
    Int.cast_natCast, Int.cast_one] at hZ
  rw [hR1, hR2, hS0, ZMod.natCast_self, ZMod.wilsons_lemma,
    show ((0 : ZMod p) - 1) ^ p = -1 by rw [zero_sub]; exact Odd.neg_one_pow hodd] at hZ
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_
  push_cast
  linear_combination hZ

/-- **`thm_fermat_congruence_exceptional`**: for an odd prime `p` with `p ∤ x`,
```
(p-1)! F^{(p-1)}_0(x) ≡ x q_p(x)^{p-1} - x q_p(x)  (mod p) ,
```
stated as divisibility between the integers `z` representing `F^{(p-1)}_0(x)` and `q`
representing `q_p(x)`. A weaker form allows a constant `c ≡ 1 (mod p)` on the second term;
that constant is here shown to be `1` on the nose, in agreement with the source paper.

This is the one pair `(j, k) = (p-1, 0)` at which
`GranvilleMoore.pow_succ_dvd_collapsedCoeff_mul_pow` has an exception, so two terms of the
master expansion survive modulo `p`: `m = p - 1`, contributing `x q_p(x)^{p-1}/(p-1)!` as in
`GranvilleMoore.dvd_factorial_mul_sub_mul_pow`, and `m = p`, whose contribution is
`b x g_0(x)^p` for the integer `b` with `p A_{p-1}(p) = p^{C(p-1,2)} b`. Since
`g_0(x)^p ≡ g_0(x) ≡ q_p(x)` by Fermat and `b ≡ 1` by `dvd_sub_one_of_mul_eq`, that second
contribution is `x q_p(x)` times a unit; Wilson's theorem fixes the signs. -/
theorem dvd_factorial_mul_sub_exceptional {p : ℕ} (hp : p.Prime) (hodd : Odd p) {x : ℤ}
    (hx : ¬ (p : ℤ) ∣ x) {z q : ℤ} (hz : iteratedFermatQuot p (p - 1) 0 x = (z : ℚ))
    (hq : fermatQuotient p x = (q : ℚ)) :
    (p : ℤ) ∣ ((p - 1).factorial : ℤ) * z - (x * q ^ (p - 1) - x * q) := by
  have hfact : Fact p.Prime := ⟨hp⟩
  have hp' : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hp
  have hpz : ((p : ℤ)) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    have : p % 2 = 1 := Nat.odd_iff.mp hodd
    omega
  obtain ⟨g, hg⟩ := unitQuot_eq_intCast hp hodd hx 0
  have hgq := dvd_unitQuot_sub_fermatQuotient hp hodd hg hq
  obtain ⟨A, hA⟩ : ∃ A : ℕ → ℤ, ∀ m, collapsedCoeff p (p - 1) m = (A m : ℚ) :=
    ⟨_, collapsedCoeff_eq_intCast p (p - 1)⟩
  have hDsimp : (p - 1) * 0 + Nat.choose (p - 1 + 1) 2 = Nat.choose (p - 1 + 1) 2 := by
    rw [Nat.mul_zero, Nat.zero_add]
  have hDC : Nat.choose (p - 1 + 1) 2 = (p - 1) + Nat.choose (p - 1) 2 := by
    rw [Nat.choose_succ_succ (p - 1) 1, Nat.choose_one_right]
  have hMC : (p : ℤ) ^ Nat.choose (p - 1 + 1) 2
      = (p : ℤ) ^ (p - 1) * (p : ℤ) ^ Nat.choose (p - 1) 2 := by rw [hDC, pow_add]
  have hppow : (p : ℤ) ^ p = (p : ℤ) ^ (p - 1) * (p : ℤ) := by
    rw [← pow_succ, show p - 1 + 1 = p by omega]
  have hMC1 : (p : ℤ) ^ (Nat.choose (p - 1 + 1) 2 + 1)
      = (p : ℤ) ^ (p - 1) * (p : ℤ) ^ Nat.choose (p - 1) 2 * (p : ℤ) := by
    rw [pow_succ, hMC]
  have hG1 : ((p : ℤ) ^ (0 + 1) * g) ^ (p - 1) = (p : ℤ) ^ (p - 1) * g ^ (p - 1) := by
    rw [mul_pow, ← pow_mul, Nat.zero_add, one_mul]
  have hG2 : ((p : ℤ) ^ (0 + 1) * g) ^ p = (p : ℤ) ^ (p - 1) * (p : ℤ) * g ^ p := by
    rw [mul_pow, ← pow_mul, Nat.zero_add, one_mul, hppow]
  have hjE : (p - 1) ∈ range (frobeniusExponent p (p - 1) + 1) :=
    mem_range.mpr (Nat.lt_succ_of_le (le_frobeniusExponent (by omega) (p - 1)))
  have hpfe : p ≤ frobeniusExponent p (p - 1) := by
    have h2 : frobeniusExponent p 2 = 1 + p := by
      rw [frobeniusExponent_eq_sum, Finset.sum_range_succ, Finset.sum_range_one]
      simp
    have := frobeniusExponent_le p (show 2 ≤ p - 1 by omega)
    omega
  have hpE : p ∈ (range (frobeniusExponent p (p - 1) + 1)).erase (p - 1) :=
    Finset.mem_erase.mpr ⟨by omega, mem_range.mpr (by omega)⟩
  obtain ⟨R, hR⟩ : (p : ℤ) ^ ((p - 1) * 0 + Nat.choose (p - 1 + 1) 2 + 1)
      ∣ ∑ m ∈ ((range (frobeniusExponent p (p - 1) + 1)).erase (p - 1)).erase p,
          A m * ((p : ℤ) ^ (0 + 1) * g) ^ m := by
    refine Finset.dvd_sum fun m hm => ?_
    have hmp : m ≠ p := Finset.ne_of_mem_erase hm
    have hmj : m ≠ p - 1 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hm)
    rw [show A m * ((p : ℤ) ^ (0 + 1) * g) ^ m = (A m * (p : ℤ) ^ (m * (0 + 1))) * g ^ m by
      rw [mul_pow, ← pow_mul, mul_comm (0 + 1) m]; ring]
    rcases lt_or_gt_of_ne hmj with h | h
    · have h0 : ((A m : ℤ) : ℚ) = 0 := by
        rw [← hA m]; exact collapsedCoeff_eq_zero hp.two_le h
      rw [show A m = 0 from by exact_mod_cast h0, zero_mul, zero_mul]
      exact dvd_zero _
    · exact (pow_succ_dvd_collapsedCoeff_mul_pow hp hodd (le_refl _) h
        (Or.inl hmp) (hA m)).mul_right _
  have hnum := (numerator_eq_pow_mul hp hz).symm.trans
    (numerator_eq_mul_sum hp.ne_zero hg (p - 1) hA)
  rw [← Finset.add_sum_erase _ (fun m => A m * ((p : ℤ) ^ (0 + 1) * g) ^ m) hjE,
    ← Finset.add_sum_erase _ (fun m => A m * ((p : ℤ) ^ (0 + 1) * g) ^ m) hpE, hR, hDsimp,
    hMC, hMC1, show x ^ p ^ 0 = x by rw [pow_zero, pow_one], hG1, hG2] at hnum
  obtain ⟨a, ha⟩ := exists_int_factorial_mul_pow_mul_collapsedCoeff_self hp.two_le (p - 1)
  rw [hA (p - 1)] at ha
  have hWA : (((p - 1).factorial : ℕ) : ℤ) * ((p : ℤ) - 1) ^ (p - 1) * A (p - 1)
      = (p : ℤ) ^ Nat.choose (p - 1) 2 * (((p : ℤ) - 1) ^ (p - 1) + (p : ℤ) * a) := by
    exact_mod_cast ha
  obtain ⟨b, hbdvd⟩ := pow_dvd_collapsedCoeff_mul_pow (k := 0) hp hodd (le_refl (p - 1))
    (show p - 1 ≤ p by omega) (hA p)
  rw [show p * (0 + 1) = p by omega, hDsimp, hMC, hppow] at hbdvd
  have hb : (p : ℤ) * A p = (p : ℤ) ^ Nat.choose (p - 1) 2 * b := by
    refine mul_left_cancel₀ (pow_ne_zero (p - 1) hpz) ?_
    linear_combination hbdvd
  have hb1 := dvd_sub_one_of_mul_eq hp hodd (hA p) hb
  have hM : (p : ℤ) ∣ (((p - 1).factorial : ℕ) : ℤ) * ((p : ℤ) - 1) ^ (p - 1) * z
      - x * (((p : ℤ) - 1) ^ (p - 1) + (p : ℤ) * a) * g ^ (p - 1)
      - x * (((p - 1).factorial : ℕ) : ℤ) * ((p : ℤ) - 1) ^ (p - 1) * b * g ^ p := by
    refine ⟨x * ((((p - 1).factorial : ℕ) : ℤ) * ((p : ℤ) - 1) ^ (p - 1)) * R, ?_⟩
    refine mul_left_cancel₀ (mul_ne_zero (pow_ne_zero (p - 1) hpz)
      (pow_ne_zero (Nat.choose (p - 1) 2) hpz)) ?_
    linear_combination ((((p - 1).factorial : ℕ) : ℤ) * ((p : ℤ) - 1) ^ (p - 1)) * hnum
      + (x * (p : ℤ) ^ (p - 1) * g ^ (p - 1)) * hWA
      + (x * (((p - 1).factorial : ℕ) : ℤ) * ((p : ℤ) - 1) ^ (p - 1) * (p : ℤ) ^ (p - 1)
          * g ^ p) * hb
  have hZ : (p : ℤ) ∣ ((p : ℤ) - 1) ^ (p - 1) *
        ((((p - 1).factorial : ℕ) : ℤ) * z - (x * q ^ (p - 1) - x * q))
      - ((((p - 1).factorial : ℕ) : ℤ) * ((p : ℤ) - 1) ^ (p - 1) * z
        - x * (((p : ℤ) - 1) ^ (p - 1) + (p : ℤ) * a) * g ^ (p - 1)
        - x * (((p - 1).factorial : ℕ) : ℤ) * ((p : ℤ) - 1) ^ (p - 1) * b * g ^ p) := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_
    have hgq' : ((g : ℤ) : ZMod p) = ((q : ℤ) : ZMod p) := by
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (g - q) p).mpr hgq
      push_cast at h
      linear_combination h
    have hb' : ((b : ℤ) : ZMod p) = 1 := by
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (b - 1) p).mpr hb1
      push_cast at h
      linear_combination h
    push_cast
    rw [ZMod.natCast_self, hgq', hb', ZMod.wilsons_lemma, ZMod.pow_card,
      show ((0 : ZMod p) - 1) ^ (p - 1) = 1 by
        rw [zero_sub]; exact Even.neg_one_pow (Nat.Odd.sub_odd hodd odd_one)]
    ring
  have hfin : (p : ℤ) ∣ ((p : ℤ) - 1) ^ (p - 1) *
      ((((p - 1).factorial : ℕ) : ℤ) * z - (x * q ^ (p - 1) - x * q)) := by
    have h := dvd_add hZ hM
    rwa [sub_add_cancel] at h
  rcases hp'.dvd_mul.mp hfin with h | h
  · exact absurd h (not_dvd_natCast_sub_one_pow hp (p - 1))
  · exact h

end GranvilleMoore
