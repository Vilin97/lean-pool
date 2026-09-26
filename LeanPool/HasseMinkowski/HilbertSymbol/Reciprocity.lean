/-
Copyright (c) 2026 jayyswan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jayyswan
-/
module

public import LeanPool.HasseMinkowski.HilbertSymbol.Padic
public import LeanPool.HasseMinkowski.HilbertSymbol.Two
public import LeanPool.HasseMinkowski.HilbertSymbol.Real
public import LeanPool.HasseMinkowski.RatSquares
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Global properties of the Hilbert symbol over `ℚ`

The Hilbert symbol `(a,b)_v` is defined at every place `v` of `ℚ` — the finite places
`v = p` (a prime, giving `ℚ_[p]`) and the archimedean place `v = ∞` (giving `ℝ`).

This file records the two global properties:

* `almost_all_one` — for fixed nonzero `a b : ℚ`, the symbol `(a,b)_p` is `1` for all but
  finitely many primes `p`.  This is a genuinely local fact: for `p` not dividing the
  numerator or denominator of `a` or `b`, both arguments are `p`-adic units, and the
  case `00` of Serre's formula gives `1`.

* Hilbert reciprocity `∏_v (a,b)_v = 1` (`hilbertReciprocity`).  The hard input is
  quadratic reciprocity (`legendreSym.quadratic_reciprocity`); the proof reduces to the
  square-class generators `-1` and the primes, using the case in which one argument is a
  square (`prod_eq_one_of_isSquare`, where every local symbol is `1`) as a step.
-/

public section

namespace HasseMinkowski

open Filter
attribute [local instance] Classical.propDecidable

/-- A prime bundled as a natural number carries its own `Fact` instance. -/
instance instFactPrimeCoeNat (p : Nat.Primes) : Fact (Nat.Prime (p : ℕ)) := ⟨p.2⟩

/-! ### Almost all local symbols are trivial

For a rational `q`, `padicValRat p q = 0` precisely when `p` divides neither the numerator
nor the denominator of `q`; such a `q` is a `p`-adic unit.  There are only finitely many
primes dividing a fixed nonzero rational, so for fixed `a, b` the symbol `(a,b)_p` is `1`
for all but finitely many `p`. -/

/-- The finite set of "bad" primes: those dividing the numerator or denominator of `a` or
`b`, together with `2` (where the odd-`p` formula does not apply). -/
private noncomputable def badPrimes (a b : ℚ) : Finset Nat.Primes :=
  let m : ℕ := a.num.natAbs * a.den * b.num.natAbs * b.den
  insert ⟨2, Nat.prime_two⟩
    (((m.divisors.filter Nat.Prime).attach).image
      (fun x => ⟨x.1, (Finset.mem_filter.mp x.2).2⟩))

-- Theorem: for fixed nonzero `a b : ℚ`, the Hilbert symbol `(a,b)_p` is `1` for all but
-- finitely many primes `p`.
theorem almost_all_one {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∀ᶠ p : Nat.Primes in Filter.cofinite,
      hilbertSym (a : ℚ_[p]) (b : ℚ_[p]) = 1 := by
  let m : ℕ := a.num.natAbs * a.den * b.num.natAbs * b.den
  have hnum_a : a.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr ha)
  have hden_a : a.den ≠ 0 := a.den_ne_zero
  have hnum_b : b.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hb)
  have hden_b : b.den ≠ 0 := b.den_ne_zero
  have hm : m ≠ 0 := by
    dsimp only [m]
    positivity
  refine (Finset.eventually_cofinite_notMem (badPrimes a b)).mono ?_
  intro p hp
  -- `p` divides neither the numerators nor the denominators of `a`, `b`, and `p ≠ 2`.
  have hpdvd : ¬ (p : ℕ) ∣ m := by
    intro hdvd
    apply hp
    dsimp only [badPrimes]
    refine Finset.mem_insert.mpr (Or.inr ?_)
    refine Finset.mem_image.mpr
      ⟨⟨(p : ℕ), Finset.mem_filter.mpr
          ⟨Nat.mem_divisors.mpr ⟨hdvd, hm⟩, p.2⟩⟩,
        Finset.mem_attach _ _, Subtype.ext rfl⟩
  have h2 : (p : ℕ) ≠ 2 := by
    intro h
    apply hp
    dsimp only [badPrimes]
    exact Finset.mem_insert.mpr (Or.inl (Subtype.ext h))
  have ha_num : ¬ (p : ℕ) ∣ a.num.natAbs := fun h =>
    hpdvd (by
      dsimp only [m]
      exact dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h a.den) b.num.natAbs) b.den)
  have ha_den : ¬ (p : ℕ) ∣ a.den := fun h =>
    hpdvd (by
      dsimp only [m]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h a.num.natAbs)
        b.num.natAbs) b.den)
  have hb_num : ¬ (p : ℕ) ∣ b.num.natAbs := fun h =>
    hpdvd (by
      dsimp only [m]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h (a.num.natAbs * a.den)) b.den)
  have hb_den : ¬ (p : ℕ) ∣ b.den := fun h =>
    hpdvd (by
      dsimp only [m]
      exact dvd_mul_of_dvd_right h ((a.num.natAbs * a.den) * b.num.natAbs))
  -- Both casts are `p`-adic units.
  have hv_a : Padic.valuation (a : ℚ_[p]) = 0 := by
    rw [Padic.valuation_ratCast, padicValRat_def]
    rw [show padicValInt (p : ℕ) a.num = padicValNat (p : ℕ) a.num.natAbs from rfl,
      padicValNat.eq_zero_of_not_dvd ha_num, padicValNat.eq_zero_of_not_dvd ha_den]
    norm_num
  have hv_b : Padic.valuation (b : ℚ_[p]) = 0 := by
    rw [Padic.valuation_ratCast, padicValRat_def]
    rw [show padicValInt (p : ℕ) b.num = padicValNat (p : ℕ) b.num.natAbs from rfl,
      padicValNat.eq_zero_of_not_dvd hb_num, padicValNat.eq_zero_of_not_dvd hb_den]
    norm_num
  have ha' : (a : ℚ_[p]) ≠ 0 := by
    exact_mod_cast ha
  have hb' : (b : ℚ_[p]) ≠ 0 := by
    exact_mod_cast hb
  rw [hilbertSym_padic_odd_eq (p := (p : ℕ)) h2 ha' hb', hv_a, hv_b]
  simp [parityPow]

-- Theorem: the set of primes at which `(a,b)_p` is nontrivial is finite.
theorem finite_nontrivial_hilbertSym {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) :
    {p : Nat.Primes | hilbertSym (a : ℚ_[p]) (b : ℚ_[p]) ≠ 1}.Finite :=
  Filter.eventually_cofinite.mp (almost_all_one ha hb)

/-! ### Corollaries: squares give the trivial symbol

If `a` is a nonzero rational square, then `(a,b)_v = 1` at *every* place `v` (both the
finite places and the archimedean one), because the conic `z² - a x² - b y² = 0` then has
the obvious point `(c, 1, 0)` with `a = c²`.  Consequently the product over all places is
`1`; this is the special case of Hilbert reciprocity that needs no quadratic reciprocity. -/

-- Theorem: if `a` is a nonzero rational square then `(a,b)_p = 1` for every prime `p`.
theorem hilbertSym_rat_eq_one_of_isSquare_left {a b : ℚ} (ha0 : a ≠ 0) (ha : IsSquare a)
    (hb : b ≠ 0) (p : Nat.Primes) :
    hilbertSym (a : ℚ_[p]) (b : ℚ_[p]) = 1 := by
  obtain ⟨c, hc⟩ := ha
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact ha0 (by rw [hc, mul_zero])
  have h : (a : ℚ_[p]) = (c : ℚ_[p]) ^ 2 := by
    rw [hc]; push_cast; ring
  rw [h]
  exact hilbertSym_sq_left (Rat.cast_ne_zero.mpr hc0) (Rat.cast_ne_zero.mpr hb)

-- Theorem: Hilbert reciprocity for the case where one argument is a square: the product of
-- all local symbols (including the archimedean one) is `1`.
theorem prod_eq_one_of_isSquare_left {a b : ℚ} (ha0 : a ≠ 0) (ha : IsSquare a)
    (hb : b ≠ 0) :
    (∏ᶠ p : Nat.Primes, hilbertSym (a : ℚ_[p]) (b : ℚ_[p]))
      * hilbertSym (a : ℝ) (b : ℝ) = 1 := by
  obtain ⟨c, hc⟩ := ha
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact ha0 (by rw [hc, mul_zero])
  have hP : ∀ p : Nat.Primes, hilbertSym (a : ℚ_[p]) (b : ℚ_[p]) = 1 :=
    fun p => hilbertSym_rat_eq_one_of_isSquare_left ha0 ⟨c, hc⟩ hb p
  have hR : (a : ℝ) = (c : ℝ) ^ 2 := by
    rw [hc]; push_cast; ring
  rw [finprod_eq_one_of_forall_eq_one hP, hR,
    hilbertSym_sq_left (Rat.cast_ne_zero.mpr hc0) (Rat.cast_ne_zero.mpr hb), one_mul]

-- Theorem: Hilbert reciprocity for the case where the second argument is a square.
theorem prod_eq_one_of_isSquare_right {a b : ℚ} (ha : a ≠ 0) (hb0 : b ≠ 0)
    (hb : IsSquare b) :
    (∏ᶠ p : Nat.Primes, hilbertSym (a : ℚ_[p]) (b : ℚ_[p]))
      * hilbertSym (a : ℝ) (b : ℝ) = 1 := by
  have hprod : (∏ᶠ p : Nat.Primes, hilbertSym (a : ℚ_[p]) (b : ℚ_[p]))
      = ∏ᶠ p : Nat.Primes, hilbertSym (b : ℚ_[p]) (a : ℚ_[p]) :=
    finprod_congr (fun p => hilbertSym_comm _ _)
  rw [hprod, hilbertSym_comm (a : ℝ) (b : ℝ)]
  exact prod_eq_one_of_isSquare_left hb0 hb ha

-- Theorem: Hilbert reciprocity holds as soon as *either* argument is a square.
theorem prod_eq_one_of_isSquare {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : IsSquare a ∨ IsSquare b) :
    (∏ᶠ p : Nat.Primes, hilbertSym (a : ℚ_[p]) (b : ℚ_[p]))
      * hilbertSym (a : ℝ) (b : ℝ) = 1 :=
  h.elim (prod_eq_one_of_isSquare_left ha · hb) (prod_eq_one_of_isSquare_right ha hb ·)

/-! ### The general statement (not proved here)

Hilbert reciprocity — the product of `(a,b)_v` over *all* places `v` of `ℚ` equals `1` —
is the deep quadratic-reciprocity input.  Its proof requires the full explicit formulas at
every place (including `p = 2`, where only the unit case is available locally) and the
quadratic reciprocity law assembled over all primes; that is beyond what this file
formalises.  We record the statement as a `Prop` for downstream reference. -/

/-- Hilbert reciprocity for `ℚ`: for nonzero rationals `a, b`, the product of the local
Hilbert symbols over all places (the finite places `ℚ_[p]` and the archimedean place `ℝ`)
is `1`.  Stated for reference; not proved in this file. -/
def HilbertReciprocity : Prop :=
  ∀ a b : ℚ, a ≠ 0 → b ≠ 0 →
    (∏ᶠ p : Nat.Primes, hilbertSym (a : ℚ_[p]) (b : ℚ_[p]))
      * hilbertSym (a : ℝ) (b : ℝ) = 1

/-! ### Phase 1: reduction of Hilbert reciprocity to square classes

Write `hilbertProd a b` for the product of the local symbols of `a, b` over every place of
`ℚ`.  Every local symbol is bimultiplicative in each argument, so `hilbertProd` is too; and
multiplying an argument by a nonzero square (or inverting it) leaves `hilbertProd` unchanged.
Hence `hilbertProd` factors through the square-class group `ℚ*/ℚ*²`, which is generated by
`-1` and the primes.  So Hilbert reciprocity follows from its restriction to pairs of
*generators* `g ∈ {-1} ∪ {primes}`: this is `hilbertReciprocity_of_generators`.  The generator
cases themselves (the content of quadratic reciprocity) are Phase 2. -/

/-- The product of the local Hilbert symbols of `a` and `b` over all places of `ℚ`: the
finite places `ℚ_[p]` together with the archimedean place `ℝ`. -/
noncomputable def hilbertProd (a b : ℚ) : ℤ :=
  (∏ᶠ p : Nat.Primes, hilbertSym (a : ℚ_[p]) (b : ℚ_[p])) * hilbertSym (a : ℝ) (b : ℝ)

/-- A generator of the square-class group `ℚ*/ℚ*²`: `-1` or a prime. -/
def IsGen (g : ℚ) : Prop := g = -1 ∨ ∃ p : Nat.Primes, g = (p : ℚ)

-- Theorem: for nonzero `a b : ℚ` the family `p ↦ (a,b)_p` has finite support.
private theorem hasFiniteMulSupport_hilbertSym_padic (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Function.HasFiniteMulSupport
      (fun p : Nat.Primes => hilbertSym (a : ℚ_[p]) (b : ℚ_[p])) :=
  Filter.eventually_cofinite.mp (almost_all_one ha hb)

-- Theorem: local bilinearity in the first argument, uniformly over all finite places.
private theorem hilbertSym_padic_mul_left (p : Nat.Primes) (a a' b : ℚ_[p]) :
    hilbertSym (a * a') b = hilbertSym a b * hilbertSym a' b := by
  by_cases hp : (p : ℕ) = 2
  · obtain rfl : p = ⟨2, Nat.prime_two⟩ := Subtype.ext hp
    exact hilbertSym_padic_two_mul_left a a' b
  · exact hilbertSym_padic_odd_mul_left hp a a' b

-- Theorem: local bilinearity in the second argument, uniformly over all finite places.
private theorem hilbertSym_padic_mul_right (p : Nat.Primes) (a b b' : ℚ_[p]) :
    hilbertSym a (b * b') = hilbertSym a b * hilbertSym a b' := by
  rw [hilbertSym_comm a (b * b'), hilbertSym_comm a b, hilbertSym_comm a b']
  exact hilbertSym_padic_mul_left p b b' a

-- Theorem: `hilbertProd` is multiplicative in the first argument.
theorem hilbertProd_mul_left (a a' b : ℚ) (ha : a ≠ 0) (ha' : a' ≠ 0) (hb : b ≠ 0) :
    hilbertProd (a * a') b = hilbertProd a b * hilbertProd a' b := by
  unfold hilbertProd
  have hcast : ∀ p : Nat.Primes, ((a * a' : ℚ) : ℚ_[p]) = (a : ℚ_[p]) * (a' : ℚ_[p]) :=
    fun p => by push_cast; ring
  rw [show (∏ᶠ p : Nat.Primes, hilbertSym ((a * a' : ℚ) : ℚ_[p]) (b : ℚ_[p]))
      = ∏ᶠ p : Nat.Primes, (hilbertSym (a : ℚ_[p]) (b : ℚ_[p])
          * hilbertSym (a' : ℚ_[p]) (b : ℚ_[p])) from
    finprod_congr (fun p => by rw [hcast p]; exact hilbertSym_padic_mul_left p _ _ _)]
  rw [finprod_mul_distrib (hasFiniteMulSupport_hilbertSym_padic a b ha hb)
    (hasFiniteMulSupport_hilbertSym_padic a' b ha' hb)]
  have hreal : ((a * a' : ℚ) : ℝ) = (a : ℝ) * (a' : ℝ) := by push_cast; ring
  rw [hreal, hilbertSym_real_mul_left]
  ring

-- Theorem: `hilbertProd` is multiplicative in the second argument.
theorem hilbertProd_mul_right (a b b' : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0) :
    hilbertProd a (b * b') = hilbertProd a b * hilbertProd a b' := by
  unfold hilbertProd
  have hcast : ∀ p : Nat.Primes, ((b * b' : ℚ) : ℚ_[p]) = (b : ℚ_[p]) * (b' : ℚ_[p]) :=
    fun p => by push_cast; ring
  rw [show (∏ᶠ p : Nat.Primes, hilbertSym (a : ℚ_[p]) ((b * b' : ℚ) : ℚ_[p]))
      = ∏ᶠ p : Nat.Primes, (hilbertSym (a : ℚ_[p]) (b : ℚ_[p])
          * hilbertSym (a : ℚ_[p]) (b' : ℚ_[p])) from
    finprod_congr (fun p => by rw [hcast p]; exact hilbertSym_padic_mul_right p _ _ _)]
  rw [finprod_mul_distrib (hasFiniteMulSupport_hilbertSym_padic a b ha hb)
    (hasFiniteMulSupport_hilbertSym_padic a b' ha hb')]
  have hreal : ((b * b' : ℚ) : ℝ) = (b : ℝ) * (b' : ℝ) := by push_cast; ring
  have hreal_mul : hilbertSym (a : ℝ) ((b : ℝ) * (b' : ℝ))
      = hilbertSym (a : ℝ) (b : ℝ) * hilbertSym (a : ℝ) (b' : ℝ) := by
    rw [hilbertSym_comm (a : ℝ) ((b : ℝ) * (b' : ℝ)), hilbertSym_real_mul_left,
      hilbertSym_comm (b : ℝ) (a : ℝ), hilbertSym_comm (b' : ℝ) (a : ℝ)]
  rw [hreal, hreal_mul]
  ring

-- Theorem: `hilbertProd` is symmetric in its two arguments.
theorem hilbertProd_comm (a b : ℚ) : hilbertProd a b = hilbertProd b a := by
  unfold hilbertProd
  rw [finprod_congr (fun p => hilbertSym_comm _ _), hilbertSym_comm]

-- Theorem: `hilbertProd a 1 = 1` for nonzero `a`.
theorem hilbertProd_one_right (a : ℚ) (ha : a ≠ 0) : hilbertProd a 1 = 1 := by
  unfold hilbertProd
  have hp : ∀ p : Nat.Primes, hilbertSym (a : ℚ_[p]) (((1 : ℚ) : ℚ_[p])) = 1 := fun p => by
    simpa using hilbertSym_sq_right (a := (a : ℚ_[p])) (b := (1 : ℚ_[p]))
      (Rat.cast_ne_zero.mpr ha) one_ne_zero
  rw [finprod_congr (fun p => hp p),
    finprod_eq_one_of_forall_eq_one (fun _ : Nat.Primes => rfl)]
  have hr : hilbertSym (a : ℝ) (((1 : ℚ) : ℝ)) = 1 := by
    simpa using hilbertSym_sq_right (a := (a : ℝ)) (b := (1 : ℝ))
      (Rat.cast_ne_zero.mpr ha) one_ne_zero
  rw [hr, one_mul]

-- Theorem: `hilbertProd 1 b = 1` for nonzero `b`.
theorem hilbertProd_one_left (b : ℚ) (hb : b ≠ 0) : hilbertProd 1 b = 1 := by
  unfold hilbertProd
  have hp : ∀ p : Nat.Primes, hilbertSym (((1 : ℚ) : ℚ_[p])) (b : ℚ_[p]) = 1 := fun p => by
    simpa using hilbertSym_sq_left (a := (1 : ℚ_[p])) (b := (b : ℚ_[p]))
      one_ne_zero (Rat.cast_ne_zero.mpr hb)
  rw [finprod_congr (fun p => hp p),
    finprod_eq_one_of_forall_eq_one (fun _ : Nat.Primes => rfl)]
  have hr : hilbertSym (((1 : ℚ) : ℝ)) (b : ℝ) = 1 := by
    simpa using hilbertSym_sq_left (a := (1 : ℝ)) (b := (b : ℝ))
      one_ne_zero (Rat.cast_ne_zero.mpr hb)
  rw [hr, one_mul]

-- Theorem: multiplying the second argument by a nonzero square leaves `hilbertProd` unchanged.
theorem hilbertProd_mul_square_right (a b c : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    hilbertProd a (b * c ^ 2) = hilbertProd a b := by
  rw [hilbertProd_mul_right a b (c ^ 2) ha hb (pow_ne_zero 2 hc)]
  have h : hilbertProd a (c ^ 2) = 1 :=
    prod_eq_one_of_isSquare_right ha (pow_ne_zero 2 hc) ⟨c, by ring⟩
  rw [h, mul_one]

-- Theorem: multiplying the first argument by a nonzero square leaves `hilbertProd` unchanged.
theorem hilbertProd_mul_square_left (a c b : ℚ) (ha : a ≠ 0) (hc : c ≠ 0) (hb : b ≠ 0) :
    hilbertProd (a * c ^ 2) b = hilbertProd a b := by
  rw [hilbertProd_mul_left a (c ^ 2) b ha (pow_ne_zero 2 hc) hb]
  have h : hilbertProd (c ^ 2) b = 1 :=
    prod_eq_one_of_isSquare_left (pow_ne_zero 2 hc) ⟨c, by ring⟩ hb
  rw [h, mul_one]

-- Theorem: inverting the first argument leaves `hilbertProd` unchanged.
theorem hilbertProd_inv_left (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertProd a⁻¹ b = hilbertProd a b := by
  have h : a = a⁻¹ * a ^ 2 := by field_simp
  have h2 : hilbertProd a b = hilbertProd a⁻¹ b := by
    conv_lhs => rw [h]
    rw [hilbertProd_mul_left a⁻¹ (a ^ 2) b (inv_ne_zero ha) (pow_ne_zero 2 ha) hb]
    have h3 : hilbertProd (a ^ 2) b = 1 :=
      prod_eq_one_of_isSquare_left (pow_ne_zero 2 ha) ⟨a, by ring⟩ hb
    rw [h3, mul_one]
  exact h2.symm

-- Theorem: inverting the second argument leaves `hilbertProd` unchanged.
theorem hilbertProd_inv_right (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertProd a b⁻¹ = hilbertProd a b := by
  rw [hilbertProd_comm a b⁻¹, hilbertProd_inv_left b a hb ha, hilbertProd_comm]

-- Theorem: `hilbertProd` is multiplicative over a finite product in the first argument.
theorem hilbertProd_finset_prod_left {ι : Type*} (S : Finset ι) (f : ι → ℚ) (b : ℚ)
    (hf : ∀ i ∈ S, f i ≠ 0) (hb : b ≠ 0) :
    hilbertProd (∏ i ∈ S, f i) b = ∏ i ∈ S, hilbertProd (f i) b := by
  induction S using Finset.induction with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, hilbertProd_one_left b hb]
  | insert i S hi ih =>
      have hfi : f i ≠ 0 := hf i (Finset.mem_insert_self i S)
      have hfS : ∀ j ∈ S, f j ≠ 0 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
      have hprod : (∏ j ∈ S, f j) ≠ 0 := Finset.prod_ne_zero_iff.mpr hfS
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        hilbertProd_mul_left (f i) (∏ j ∈ S, f j) b hfi hprod hb, ih hfS]

-- Theorem: `hilbertProd` is multiplicative over a finite product in the second argument.
theorem hilbertProd_finset_prod_right {ι : Type*} (S : Finset ι) (f : ι → ℚ) (a : ℚ)
    (hf : ∀ i ∈ S, f i ≠ 0) (ha : a ≠ 0) :
    hilbertProd a (∏ i ∈ S, f i) = ∏ i ∈ S, hilbertProd a (f i) := by
  induction S using Finset.induction with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, hilbertProd_one_right a ha]
  | insert i S hi ih =>
      have hfi : f i ≠ 0 := hf i (Finset.mem_insert_self i S)
      have hfS : ∀ j ∈ S, f j ≠ 0 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
      have hprod : (∏ j ∈ S, f j) ≠ 0 := Finset.prod_ne_zero_iff.mpr hfS
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        hilbertProd_mul_right a (f i) (∏ j ∈ S, f j) ha hfi hprod, ih hfS]

/-! ### The square-class decomposition

Every nonzero rational is a generator product times a nonzero square.  Write `q = ±u/v` with
`u = |q.num|`, `v = q.den`; apply `Nat.sq_mul_squarefree_of_pos` to `u * v`, so that
`u * v = b² · a` with `a` squarefree.  Then `u/v = a · (b/v)²`, and the squarefree `a` is the
product of its (prime) factors. -/

-- Theorem: a generator of `ℚ*/ℚ*²` is nonzero.
theorem IsGen.ne_zero {g : ℚ} (hg : IsGen g) : g ≠ 0 := by
  rcases hg with rfl | ⟨p, rfl⟩
  · norm_num
  · exact_mod_cast (Nat.Prime.ne_zero p.2)

-- Theorem: every nonzero rational is a generator product times a nonzero square: `q = S.prod id
-- * s²` with every element of `S` a generator and `s ≠ 0`.
theorem exists_gen_prod_mul_sq (q : ℚ) (hq : q ≠ 0) :
    ∃ (S : Finset ℚ) (s : ℚ), (∀ g ∈ S, IsGen g) ∧ s ≠ 0 ∧ q = S.prod id * s ^ 2 := by
  set u : ℕ := q.num.natAbs with hu_def
  set v : ℕ := q.den with hv_def
  have hu : 0 < u := by
    rw [hu_def]
    exact Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hq)
  have hv : 0 < v := by
    rw [hv_def]
    exact Nat.pos_of_ne_zero q.den_ne_zero
  obtain ⟨a, b, ha, hb, hba, hsf⟩ := Nat.sq_mul_squarefree_of_pos (Nat.mul_pos hu hv)
  have hbne : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  have hvne : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv.ne'
  have hs : (b : ℚ) / (v : ℚ) ≠ 0 := div_ne_zero hbne hvne
  have habs : |q| = (u : ℚ) / (v : ℚ) := by
    rw [Rat.abs_def, ← hu_def, ← hv_def, Rat.divInt_eq_div]
    norm_num
  have h1 : (b : ℚ) ^ 2 * (a : ℚ) = (u : ℚ) * (v : ℚ) := by exact_mod_cast hba
  have hfrac : (u : ℚ) / (v : ℚ) = (a : ℚ) * ((b : ℚ) / (v : ℚ)) ^ 2 := by
    field_simp
    nlinarith [h1]
  set T : Finset ℚ := a.primeFactors.image (fun p : ℕ => (p : ℚ)) with hT_def
  have hT : T.prod id = (a : ℚ) := by
    have hinj : Set.InjOn (fun p : ℕ => (p : ℚ)) (↑a.primeFactors : Set ℕ) :=
      fun x _ y _ h => Nat.cast_injective h
    have hcast : ((∏ p ∈ a.primeFactors, p : ℕ) : ℚ)
        = ∏ p ∈ a.primeFactors, (p : ℚ) :=
      map_prod (Nat.castRingHom ℚ) (fun p => p) a.primeFactors
    rw [hT_def, Finset.prod_image (f := id) (g := fun p : ℕ => (p : ℚ)) hinj]
    simp only [id_eq]
    rw [← hcast, Nat.prod_primeFactors_of_squarefree hsf]
  have hTgen : ∀ g ∈ T, IsGen g := by
    intro g hg
    rw [hT_def] at hg
    obtain ⟨p, hp, hpg⟩ := Finset.mem_image.mp hg
    rw [← hpg]
    exact Or.inr ⟨⟨p, Nat.prime_of_mem_primeFactors hp⟩, rfl⟩
  have hneg : (-1 : ℚ) ∉ T := by
    intro hmem
    rw [hT_def] at hmem
    obtain ⟨p, hp, hp1⟩ := Finset.mem_image.mp hmem
    have hpos : (0 : ℚ) < (p : ℚ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    rw [hp1] at hpos
    norm_num at hpos
  refine ⟨(if q < 0 then insert (-1) T else T), (b : ℚ) / (v : ℚ), ?_, hs, ?_⟩
  · intro g hg
    by_cases hqneg : q < 0
    · rw [ite_eq_left hqneg] at hg
      rcases Finset.mem_insert.mp hg with h | h
      · exact Or.inl h
      · exact hTgen g h
    · rw [ite_eq_right hqneg] at hg
      exact hTgen g hg
  · by_cases hqneg : q < 0
    · have hSprod : (if q < 0 then insert (-1) T else T).prod id = -1 * T.prod id := by
        rw [ite_eq_left hqneg, Finset.prod_insert hneg]
        simp
      have hqeq : q = -|q| := by rw [abs_of_neg hqneg, neg_neg]
      calc q = -|q| := hqeq
        _ = -((u : ℚ) / (v : ℚ)) := by rw [habs]
        _ = -((a : ℚ) * ((b : ℚ) / (v : ℚ)) ^ 2) := by rw [hfrac]
        _ = (if q < 0 then insert (-1) T else T).prod id * ((b : ℚ) / (v : ℚ)) ^ 2 := by
              rw [hSprod, hT]; ring
    · have hqpos : 0 < q := lt_of_le_of_ne (le_of_not_gt hqneg) (Ne.symm hq)
      have hSprod : (if q < 0 then insert (-1) T else T).prod id = T.prod id := by
        rw [ite_eq_right hqneg]
      have hqeq : q = |q| := (abs_of_pos hqpos).symm
      calc q = |q| := hqeq
        _ = (u : ℚ) / (v : ℚ) := habs
        _ = (a : ℚ) * ((b : ℚ) / (v : ℚ)) ^ 2 := hfrac
        _ = (if q < 0 then insert (-1) T else T).prod id * ((b : ℚ) / (v : ℚ)) ^ 2 := by
              rw [hSprod, hT]

/-! ### Phase 1: reduction to the generator cases -/

-- Theorem: `hilbertProd g b = 1` for a generator `g` and any nonzero `b`, assuming the
-- generator cases of Hilbert reciprocity.
theorem hilbertProd_gen_left
    (hgen : ∀ g h : ℚ, IsGen g → IsGen h → hilbertProd g h = 1)
    (g : ℚ) (hg : IsGen g) (b : ℚ) (hb : b ≠ 0) : hilbertProd g b = 1 := by
  obtain ⟨S, s, hSgen, hs, hbdec⟩ := exists_gen_prod_mul_sq b hb
  have hg0 : g ≠ 0 := hg.ne_zero
  have hS0 : ∀ i ∈ S, id i ≠ 0 := fun i hi => (hSgen i hi).ne_zero
  have hSprod0 : S.prod id ≠ 0 := Finset.prod_ne_zero_iff.mpr hS0
  rw [hbdec, hilbertProd_mul_right g (S.prod id) (s ^ 2) hg0 hSprod0 (pow_ne_zero 2 hs)]
  rw [hilbertProd_finset_prod_right S id g hS0 hg0]
  simp only [id_eq]
  rw [Finset.prod_eq_one (fun i hi => hgen g i hg (hSgen i hi))]
  have hsq : hilbertProd g (s ^ 2) = 1 := by
    rw [← one_mul (s ^ 2), hilbertProd_mul_square_right g 1 s hg0 one_ne_zero hs,
      hilbertProd_one_right g hg0]
  rw [hsq, mul_one]

-- Theorem: `hilbertProd a b = 1` for all nonzero `a b`, assuming the generator cases.
theorem hilbertProd_eq_one
    (hgen : ∀ g h : ℚ, IsGen g → IsGen h → hilbertProd g h = 1)
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) : hilbertProd a b = 1 := by
  obtain ⟨S, s, hSgen, hs, hadec⟩ := exists_gen_prod_mul_sq a ha
  have hS0 : ∀ i ∈ S, id i ≠ 0 := fun i hi => (hSgen i hi).ne_zero
  have hSprod0 : S.prod id ≠ 0 := Finset.prod_ne_zero_iff.mpr hS0
  rw [hadec, hilbertProd_mul_left (S.prod id) (s ^ 2) b hSprod0 (pow_ne_zero 2 hs) hb]
  rw [hilbertProd_finset_prod_left S id b hS0 hb]
  simp only [id_eq]
  rw [Finset.prod_eq_one (fun i hi => hilbertProd_gen_left hgen i (hSgen i hi) b hb)]
  have hsq : hilbertProd (s ^ 2) b = 1 := by
    rw [← one_mul (s ^ 2), hilbertProd_mul_square_left 1 s b one_ne_zero hs hb,
      hilbertProd_one_left b hb]
  rw [hsq, mul_one]

-- Theorem: Hilbert reciprocity follows from its restriction to pairs of square-class
-- generators `g ∈ {-1} ∪ {primes}`.
theorem hilbertReciprocity_of_generators
    (hgen : ∀ g h : ℚ, IsGen g → IsGen h → hilbertProd g h = 1) :
    HilbertReciprocity := by
  intro a b ha hb
  change hilbertProd a b = 1
  exact hilbertProd_eq_one hgen ha hb

/-! ### Phase 2: the generator cases

`hilbertReciprocity_of_generators` reduces `HilbertReciprocity` to the values on pairs of
generators `g, h ∈ {-1} ∪ {primes}`.  Those are exactly the quadratic-reciprocity
computations:

* `hilbertProd (-1) (-1) = 1`: the archimedean and `2`-adic symbols are both `-1`, and the
  finite product over the remaining places is `-1`, so the two cancel;
* `hilbertProd (-1) p = 1`: the two non-trivial places `2` and `p` both contribute
  `(-1)^{(p-1)/2}`;
* `hilbertProd p p = 1`: the supplementary laws at `2` and at `p`;
* `hilbertProd p q = 1` for distinct primes, the quadratic reciprocity law
  `(p/q)(q/p) = (-1)^{(p-1)/2 · (q-1)/2}`
  (`Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity`).

Each case is a finite `finprod` with support among `{2, p, q}`; applying
`hilbertReciprocity_of_generators` to them yields `HilbertReciprocity` itself
(`hilbertReciprocity`, at the end of the file). -/

/-! ### Phase 2, infrastructure

`finprod_hilbertSym_eq_finset_prod` reduces the infinite product over all primes to a finite
product over an explicit small set.  `hilbertSym_padic_odd_units` handles every odd place that
divides neither argument, and `quadraticChar_padicUnit_nat` identifies the quadratic character
of the unit part of a rational prime with Mathlib's `legendreSym`. -/

/-- The prime `2`, bundled as an element of `Nat.Primes`. -/
private abbrev twoPrime : Nat.Primes := ⟨2, Nat.prime_two⟩

-- Theorem: the `p`-adic valuation of a natural number cast into `ℚ_[p]` is `0` when `p` does
-- not divide it.
private lemma padic_valuation_natCast_cast {ℓ : ℕ} [Fact (Nat.Prime ℓ)] {n : ℕ}
    (h : ¬ ℓ ∣ n) : Padic.valuation ((n : ℚ) : ℚ_[ℓ]) = 0 := by
  have hcast : ((n : ℚ) : ℚ_[ℓ]) = (n : ℚ_[ℓ]) := by norm_cast
  rw [hcast, Padic.valuation_natCast, padicValNat.eq_zero_of_not_dvd h]
  norm_num

-- Theorem: the `p`-adic valuation of `-1` is `0`.
private lemma padic_valuation_neg_one {ℓ : ℕ} [Fact (Nat.Prime ℓ)] :
    Padic.valuation (((-1 : ℚ) : ℚ_[ℓ])) = 0 := by
  rw [Padic.valuation_ratCast, show ((-1 : ℚ)) = -(1 : ℚ) by norm_num, padicValRat.neg,
    padicValRat.one]

-- Theorem: reducing an infinite product of local Hilbert symbols to a finite product, given
-- that all places outside `S` contribute `1`.
private theorem finprod_hilbertSym_eq_finset_prod {S : Finset Nat.Primes} {a b : ℚ}
    (h : ∀ ℓ : Nat.Primes, ℓ ∉ S → hilbertSym (a : ℚ_[ℓ]) (b : ℚ_[ℓ]) = 1) :
    (∏ᶠ ℓ : Nat.Primes, hilbertSym (a : ℚ_[ℓ]) (b : ℚ_[ℓ]))
      = ∏ ℓ ∈ S, hilbertSym (a : ℚ_[ℓ]) (b : ℚ_[ℓ]) := by
  refine finprod_eq_prod_of_mulSupport_subset
    (f := fun ℓ : Nat.Primes => hilbertSym (a : ℚ_[ℓ]) (b : ℚ_[ℓ])) ?_
  intro ℓ hℓ
  simp only [Function.mem_mulSupport] at hℓ
  by_contra hmem
  exact hℓ (h ℓ hmem)

-- Theorem: two `p`-adic units have trivial Hilbert symbol for odd `p`, in valuation form.
private lemma hilbertSym_padic_odd_units {ℓ : ℕ} [Fact (Nat.Prime ℓ)] (hℓ : ℓ ≠ 2)
    {a b : ℚ_[ℓ]} (ha : a ≠ 0) (hb : b ≠ 0)
    (hva : Padic.valuation a = 0) (hvb : Padic.valuation b = 0) :
    hilbertSym a b = 1 := by
  rw [hilbertSym_padic_odd_eq hℓ ha hb, hva, hvb]
  simp [parityPow]

-- Theorem: the quadratic character of the `p`-adic unit part of a rational natural number is
-- its Legendre symbol.
private lemma quadraticChar_padicUnit_nat {ℓ : ℕ} [Fact (Nat.Prime ℓ)] {n : ℕ}
    (hn : n ≠ 0) (h : ¬ ℓ ∣ n) :
    (quadraticChar (ZMod ℓ))
        (PadicInt.toZMod
          (padicUnit ((n : ℚ) : ℚ_[ℓ]) (by exact_mod_cast hn) : ℤ_[ℓ]))
      = legendreSym ℓ n := by
  have hval := padic_valuation_natCast_cast (ℓ := ℓ) h
  have hcoe : ((padicUnit ((n : ℚ) : ℚ_[ℓ]) (by exact_mod_cast hn) : ℤ_[ℓ]) : ℚ_[ℓ])
      = (n : ℚ_[ℓ]) := by
    rw [coe_padicUnit, hval, neg_zero, zpow_zero, mul_one]
    norm_cast
  have heq : (padicUnit ((n : ℚ) : ℚ_[ℓ]) (by exact_mod_cast hn) : ℤ_[ℓ])
      = (n : ℤ_[ℓ]) := by
    apply PadicInt.ext
    rw [hcoe]
    norm_cast
  rw [heq, map_natCast]
  simp only [legendreSym, Int.cast_natCast]

-- Theorem: the quadratic character of the unit part of `-1` is the Legendre symbol of `-1`.
private lemma quadraticChar_padicUnit_neg_one {ℓ : ℕ} [Fact (Nat.Prime ℓ)] :
    (quadraticChar (ZMod ℓ))
        (PadicInt.toZMod
          (padicUnit (((-1 : ℚ) : ℚ_[ℓ])) (by norm_num) : ℤ_[ℓ]))
      = legendreSym ℓ (-1) := by
  have hcoe : ((padicUnit (((-1 : ℚ) : ℚ_[ℓ])) (by norm_num) : ℤ_[ℓ]) : ℚ_[ℓ])
      = (-1 : ℚ_[ℓ]) := by
    rw [coe_padicUnit, padic_valuation_neg_one, neg_zero, zpow_zero, mul_one]
    norm_cast
  have heq : (padicUnit (((-1 : ℚ) : ℚ_[ℓ])) (by norm_num) : ℤ_[ℓ])
      = (-1 : ℤ_[ℓ]) := by
    apply PadicInt.ext
    rw [hcoe]
    norm_cast
  rw [heq, map_neg, map_one]
  simp only [legendreSym, Int.cast_neg, Int.cast_one]

/-! ### Phase 2, the `2`-adic supplementary laws

The `2`-adic unit formulas of `Two.lean` are stated for units of `ℤ_[2]`; we package an odd
natural `n` as the unit `unitTwo n`.  The three evaluations needed below are
`(-1,-1)_2 = -1`, `(-1,n)_2 = χ₄ n` and `(n,n)_2 = χ₄ n`, the last two being the
supplementary laws at `2` rewritten as values of the Dirichlet character `χ₄`. -/

-- Theorem: an odd natural number, viewed as a `2`-adic integer, is a unit.
private lemma isUnit_two_natCast {n : ℕ} (hn : ¬ 2 ∣ n) : IsUnit (n : ℤ_[2]) := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hn

-- Theorem: an odd natural number packaged as a `2`-adic unit.
private noncomputable def unitTwo (n : ℕ) (hn : ¬ 2 ∣ n) : ℤ_[2]ˣ :=
  (isUnit_two_natCast hn).unit

-- Theorem: the underlying `2`-adic number of `unitTwo n` is `n`.
private lemma coe_unitTwo (n : ℕ) (hn : ¬ 2 ∣ n) :
    ((unitTwo n hn : ℤ_[2]) : ℚ_[2]) = ((n : ℚ) : ℚ_[2]) := by
  have h : ((unitTwo n hn : ℤ_[2])) = (n : ℤ_[2]) := IsUnit.unit_spec _
  rw [h]
  norm_cast

-- Theorem: `unitTwo n` reduces to `n` modulo `4`.
private lemma unitTwo_toZModPow_two (n : ℕ) (hn : ¬ 2 ∣ n) :
    (unitTwo n hn : ℤ_[2]).toZModPow 2 = (n : ZMod 4) := by
  have h : ((unitTwo n hn : ℤ_[2])) = (n : ℤ_[2]) := IsUnit.unit_spec _
  rw [h]
  simp

-- Theorem: `unitTwo n` reduces to `n` modulo `8`.
private lemma unitTwo_toZModPow_three (n : ℕ) (hn : ¬ 2 ∣ n) :
    (unitTwo n hn : ℤ_[2]).toZModPow 3 = (n : ZMod 8) := by
  have h : ((unitTwo n hn : ℤ_[2])) = (n : ℤ_[2]) := IsUnit.unit_spec _
  rw [h]
  simp

-- Theorem: `-1`, viewed as a `2`-adic unit, is `3` modulo `4`.
private lemma negOne_toZModPow_two :
    (((-1 : ℤ_[2]ˣ) : ℤ_[2]).toZModPow 2) = (3 : ZMod 4) := by
  rw [Units.val_neg, Units.val_one, map_neg, map_one]
  decide

-- Theorem: `-1`, viewed as a `2`-adic unit, is `7` modulo `8`.
private lemma negOne_toZModPow_three :
    (((-1 : ℤ_[2]ˣ) : ℤ_[2]).toZModPow 3) = (7 : ZMod 8) := by
  rw [Units.val_neg, Units.val_one, map_neg, map_one]
  decide

-- Theorem: `parityPow b n = 1` when `n` is even.
private lemma parityPow_even' {b n : ℤ} (h : Even n) : parityPow b n = 1 := by
  rw [parityPow, ite_eq_left h]

-- Theorem: `parityPow b n = b` when `n` is odd.
private lemma parityPow_odd' {b n : ℤ} (h : ¬ Even n) : parityPow b n = b := by
  rw [parityPow, ite_eq_right h]

-- Theorem: for odd `n`, `χ₄ n` is `1` exactly when `n ≡ 1 (mod 4)`.
private lemma chi4_nat_odd (n : ℕ) (hn : ¬ 2 ∣ n) :
    ZMod.χ₄ n = if (n : ZMod 4) = 1 then 1 else -1 := by
  have hn2 : n % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · exact absurd ((Nat.dvd_iff_mod_eq_zero).mpr h) hn
    · exact h
  have hmod : (n : ZMod 4) = 1 ↔ n % 4 = 1 := by
    rw [show (1 : ZMod 4) = ((1 : ℕ) : ZMod 4) by rfl]
    rw [ZMod.natCast_eq_natCast_iff']
  rw [ZMod.χ₄_nat_eq_if_mod_four, ite_eq_right (by omega : ¬ n % 2 = 0)]
  by_cases h4 : (n : ZMod 4) = 1
  · rw [ite_eq_left h4, ite_eq_left (hmod.mp h4)]
  · rw [ite_eq_right h4, ite_eq_right (fun hh => h4 (hmod.mpr hh))]

-- Theorem: the coercion of `-1` from the units of `ℤ_[2]` agrees with the rational `-1`.
private lemma cast_neg_one_units : (((-1 : ℤ_[2]ˣ) : ℚ_[2])) = (((-1 : ℚ) : ℚ_[2])) := by
  rw [Units.val_neg, Units.val_one]
  norm_num

-- Theorem: `(-1,-1)_2 = -1`.
private lemma hilbertSym_padic_two_neg_one_neg_one :
    hilbertSym (((-1 : ℚ) : ℚ_[2])) (((-1 : ℚ) : ℚ_[2])) = -1 := by
  have h := hilbertSym_padic_two_units (-1 : ℤ_[2]ˣ) (-1 : ℤ_[2]ˣ)
  rw [cast_neg_one_units, negOne_toZModPow_two] at h
  rw [ite_eq_right (by decide : ¬ ((3 : ZMod 4) = 1 ∨ (3 : ZMod 4) = 1))] at h
  exact h

-- Theorem: `(-1,n)_2 = χ₄ n` for odd `n`.
private lemma hilbertSym_padic_two_neg_one_unit (n : ℕ) (hn : ¬ 2 ∣ n) :
    hilbertSym (((-1 : ℚ) : ℚ_[2])) (((n : ℚ) : ℚ_[2])) = ZMod.χ₄ n := by
  have h := hilbertSym_padic_two_units (-1 : ℤ_[2]ˣ) (unitTwo n hn)
  rw [cast_neg_one_units, coe_unitTwo n hn, negOne_toZModPow_two,
    unitTwo_toZModPow_two n hn] at h
  rw [chi4_nat_odd n hn, h]
  have h3 : ¬ ((3 : ZMod 4) = 1) := by decide
  by_cases h4 : (n : ZMod 4) = 1
  · rw [ite_eq_left (Or.inr h4), ite_eq_left h4]
  · rw [ite_eq_right (fun hh => hh.elim h3 h4), ite_eq_right h4]

-- Theorem: `(n,n)_2 = χ₄ n` for odd `n`.
private lemma hilbertSym_padic_two_unit_unit (n : ℕ) (hn : ¬ 2 ∣ n) :
    hilbertSym (((n : ℚ) : ℚ_[2])) (((n : ℚ) : ℚ_[2])) = ZMod.χ₄ n := by
  have h := hilbertSym_padic_two_units (unitTwo n hn) (unitTwo n hn)
  rw [coe_unitTwo n hn, unitTwo_toZModPow_two n hn] at h
  rw [chi4_nat_odd n hn, h]
  by_cases h4 : (n : ZMod 4) = 1
  · rw [ite_eq_left (Or.inl h4), ite_eq_left h4]
  · rw [ite_eq_right (fun hh => hh.elim h4 h4), ite_eq_right h4]

-- Theorem: `(-1,2)_2 = 1`.
private lemma hilbertSym_padic_two_neg_one_two :
    hilbertSym (((-1 : ℚ) : ℚ_[2])) (2 : ℚ_[2]) = 1 := by
  rw [hilbertSym_comm]
  have h := hilbertSym_two_unit_char (-1 : ℤ_[2]ˣ)
  rw [cast_neg_one_units] at h
  rw [h, show omg (-1 : ℤ_[2]ˣ) = 0 from by rw [omg, negOne_toZModPow_three]; decide]
  rw [parityPow, ite_eq_left (show Even (0 : ℤ) by decide)]

-- Theorem: `(2,2)_2 = 1`, with the explicit point `(2,1,1)`.
private lemma hilbertSym_padic_two_two_two :
    hilbertSym (2 : ℚ_[2]) (2 : ℚ_[2]) = 1 :=
  hilbertSym_eq_one_of_sol (by norm_num) (by norm_num)
    ⟨(2 : ℚ_[2]), 1, 1, by simp, by norm_num⟩

/-! ### Phase 2, the odd-prime evaluations -/

-- Theorem: the valuation of a rational prime `p` at a different prime place `ℓ` is `0`.
private lemma padic_valuation_prime_ne {ℓ p : Nat.Primes} (hp : p ≠ ℓ) :
    Padic.valuation (((p : ℚ) : ℚ_[ℓ])) = 0 :=
  padic_valuation_natCast_cast (ℓ := (ℓ : ℕ)) (n := (p : ℕ))
    (fun h => hp (Subtype.ext ((Nat.prime_dvd_prime_iff_eq ℓ.2 p.2).mp h).symm))

-- Theorem: the valuation of a rational prime `p` at its own place is `1`.
private lemma padic_valuation_prime_self (p : Nat.Primes) :
    Padic.valuation (((p : ℚ) : ℚ_[p])) = 1 := by
  rw [show (((p : ℚ) : ℚ_[p])) = ((p : ℕ) : ℚ_[p]) by norm_cast, Padic.valuation_natCast,
    padicValNat_self]
  norm_num

-- Theorem: `(-1,p)_p = (p/-1)` for odd `p`.
private lemma hilbertSym_padic_odd_neg_one_prime (ℓ : Nat.Primes) (h2 : (ℓ : ℕ) ≠ 2) :
    hilbertSym (((-1 : ℚ) : ℚ_[ℓ])) (((ℓ : ℚ) : ℚ_[ℓ])) = legendreSym (ℓ : ℕ) (-1) := by
  have ha : (((-1 : ℚ) : ℚ_[ℓ])) ≠ 0 := by norm_num
  have hb : (((ℓ : ℚ) : ℚ_[ℓ])) ≠ 0 := by
    rw [show (((ℓ : ℚ) : ℚ_[ℓ])) = ((ℓ : ℕ) : ℚ_[ℓ]) by norm_cast]
    exact_mod_cast (Nat.Prime.ne_zero ℓ.2)
  rw [hilbertSym_padic_odd_eq h2 ha hb, padic_valuation_neg_one,
    padic_valuation_prime_self ℓ]
  rw [show ((0 : ℤ) * 1) = 0 by ring,
    parityPow_even' (show Even (0 : ℤ) by decide),
    parityPow_odd' (show ¬ Even (1 : ℤ) by decide),
    parityPow_even' (show Even (0 : ℤ) by decide)]
  simp only [one_mul, mul_one]
  simpa using quadraticChar_padicUnit_neg_one

-- Theorem: `(p,p)_p = (p/-1)` for odd `p`.
private lemma hilbertSym_padic_odd_prime_self (ℓ : Nat.Primes) (h2 : (ℓ : ℕ) ≠ 2) :
    hilbertSym (((ℓ : ℚ) : ℚ_[ℓ])) (((ℓ : ℚ) : ℚ_[ℓ])) = legendreSym (ℓ : ℕ) (-1) := by
  have h := hilbertSym_padic_odd_case11 (p := (ℓ : ℕ)) h2
  have hcast : (((ℓ : ℚ) : ℚ_[ℓ])) = (((ℓ : ℕ) : ℚ_[ℓ])) := by norm_cast
  rw [hcast, h]
  simp only [legendreSym, Int.cast_neg, Int.cast_one]

/-! ### Phase 2, the generator cases -/

-- Theorem: `(-1,-1)_ℝ = -1`.
private lemma hilbertSym_real_neg_one_neg_one : hilbertSym ((-1 : ℝ)) (-1 : ℝ) = -1 := by
  rw [hilbertSym_real_eq (by norm_num) (by norm_num)]
  norm_num

-- Theorem: `(-1,x)_ℝ = 1` for positive `x`.
private lemma hilbertSym_real_neg_one_pos (x : ℝ) (hx : 0 < x) : hilbertSym (-1 : ℝ) x = 1 := by
  rw [hilbertSym_real_eq (by norm_num) (ne_of_gt hx), ite_eq_left (Or.inr hx)]

-- Theorem: `(x,y)_ℝ = 1` for positive `x`, `y`.
private lemma hilbertSym_real_pos_pos (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    hilbertSym x y = 1 := by
  rw [hilbertSym_real_eq (ne_of_gt hx) (ne_of_gt hy), ite_eq_left (Or.inl hx)]

-- Theorem: a rational prime is positive as a real number.
private lemma prime_cast_pos (p : Nat.Primes) : (0 : ℝ) < ((p : ℚ) : ℝ) := by
  rw [show (((p : ℚ)) : ℝ) = ((p : ℕ) : ℝ) by norm_cast]
  exact_mod_cast p.2.pos

-- Theorem: the cast of a rational prime into `ℚ_[ℓ]` is nonzero.
private lemma prime_ratCast_ne_zero (p : Nat.Primes) (ℓ : ℕ) [Fact (Nat.Prime ℓ)] :
    (((p : ℚ)) : ℚ_[ℓ]) ≠ 0 :=
  Rat.cast_ne_zero.mpr (by exact_mod_cast (Nat.Prime.ne_zero p.2))

-- Theorem: the valuation of `2` at a prime place `ℓ ≠ 2` is `0`.
private lemma padic_valuation_two_cast {ℓ : Nat.Primes} (h2 : (ℓ : ℕ) ≠ 2) :
    Padic.valuation (((twoPrime : ℚ) : ℚ_[ℓ])) = 0 :=
  padic_valuation_natCast_cast (ℓ := (ℓ : ℕ)) (n := 2)
    (fun h => h2 ((Nat.prime_dvd_prime_iff_eq ℓ.2 Nat.prime_two).mp h))

-- Theorem: no prime `p ≠ 2` is divisible by `2`.
private lemma not_two_dvd_of_ne_two {p : Nat.Primes} (hp2 : (p : ℕ) ≠ 2) : ¬ 2 ∣ (p : ℕ) :=
  fun h => hp2 (((Nat.prime_dvd_prime_iff_eq Nat.prime_two p.2).mp h).symm)

-- Theorem: `(p/-1)^2 = 1` for a prime `p ≠ 2`.
private lemma legendreSym_neg_one_sq (p : Nat.Primes) (hp2 : (p : ℕ) ≠ 2) :
    legendreSym (p : ℕ) (-1) * legendreSym (p : ℕ) (-1) = 1 := by
  have hpmod : (p : ℕ) % 2 = 1 := (Nat.Prime.eq_two_or_odd p.2).resolve_left hp2
  rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_eq_if_mod_four,
    ite_eq_right (by omega : ¬ (p : ℕ) % 2 = 0)]
  split_ifs <;> norm_num

-- Theorem: `p ≠ twoPrime`.
private lemma prime_ne_twoPrime {p : Nat.Primes} (hp2 : (p : ℕ) ≠ 2) : p ≠ twoPrime :=
  fun h => hp2 (congrArg Subtype.val h)

-- Theorem: Hilbert reciprocity for the pair `(-1,-1)`.
theorem hilbertProd_neg_one_neg_one : hilbertProd (-1) (-1) = 1 := by
  unfold hilbertProd
  rw [finprod_hilbertSym_eq_finset_prod (S := {twoPrime}) ?_]
  · rw [Finset.prod_singleton]
    rw [show hilbertSym (((-1 : ℚ) : ℚ_[twoPrime])) (((-1 : ℚ) : ℚ_[twoPrime])) = -1 by
      exact hilbertSym_padic_two_neg_one_neg_one]
    rw [show hilbertSym (((-1 : ℚ) : ℝ)) (((-1 : ℚ) : ℝ)) = -1 by
      rw [show (((-1 : ℚ)) : ℝ) = (-1 : ℝ) by norm_num]
      exact hilbertSym_real_neg_one_neg_one]
    norm_num
  · intro ℓ hℓ
    have h2 : (ℓ : ℕ) ≠ 2 := fun h => hℓ (by
      rw [show ℓ = twoPrime from Subtype.ext h]
      exact Finset.mem_singleton_self _)
    exact hilbertSym_padic_odd_units h2 (by norm_num) (by norm_num)
      padic_valuation_neg_one padic_valuation_neg_one

-- Theorem: Hilbert reciprocity for the pair `(-1,p)`.
theorem hilbertProd_neg_one_prime (p : Nat.Primes) : hilbertProd (-1) (p : ℚ) = 1 := by
  by_cases hp2 : (p : ℕ) = 2
  · obtain rfl : p = twoPrime := Subtype.ext hp2
    unfold hilbertProd
    rw [finprod_hilbertSym_eq_finset_prod (S := {twoPrime}) ?_]
    · rw [Finset.prod_singleton]
      rw [show hilbertSym (((-1 : ℚ) : ℚ_[twoPrime])) (((twoPrime : ℚ) : ℚ_[twoPrime]))
          = 1 by exact hilbertSym_padic_two_neg_one_two]
      rw [show hilbertSym (((-1 : ℚ) : ℝ)) (((twoPrime : ℚ) : ℝ)) = 1 by
        simpa using hilbertSym_real_neg_one_pos 2 (by norm_num)]
      norm_num
    · intro ℓ hℓ
      have h2 : (ℓ : ℕ) ≠ 2 := fun h => hℓ (by
        rw [show ℓ = twoPrime from Subtype.ext h]
        exact Finset.mem_singleton_self _)
      exact hilbertSym_padic_odd_units h2 (by norm_num) (prime_ratCast_ne_zero twoPrime ℓ)
        padic_valuation_neg_one (padic_valuation_two_cast h2)
  · have hne : twoPrime ≠ p := (prime_ne_twoPrime hp2).symm
    unfold hilbertProd
    rw [finprod_hilbertSym_eq_finset_prod (S := {twoPrime, p}) ?_]
    · rw [Finset.prod_insert (by simpa [Finset.mem_singleton] using hne),
        Finset.prod_singleton]
      have hchi : ZMod.χ₄ (p : ℕ) = legendreSym (p : ℕ) (-1) :=
        (legendreSym.at_neg_one hp2).symm
      have h2val : hilbertSym (((-1 : ℚ) : ℚ_[twoPrime])) (((p : ℚ) : ℚ_[twoPrime]))
          = legendreSym (p : ℕ) (-1) := by
        have h := hilbertSym_padic_two_neg_one_unit (p : ℕ) (not_two_dvd_of_ne_two hp2)
        rw [hchi] at h
        exact h
      have hpval : hilbertSym (((-1 : ℚ) : ℚ_[p])) (((p : ℚ) : ℚ_[p]))
          = legendreSym (p : ℕ) (-1) :=
        hilbertSym_padic_odd_neg_one_prime p hp2
      have hreal : hilbertSym (((-1 : ℚ) : ℝ)) (((p : ℚ) : ℝ)) = 1 := by
        rw [show (((-1 : ℚ)) : ℝ) = (-1 : ℝ) by norm_num]
        exact hilbertSym_real_neg_one_pos _ (prime_cast_pos p)
      have hsq : legendreSym (p : ℕ) (-1) * legendreSym (p : ℕ) (-1) = 1 :=
        legendreSym_neg_one_sq p hp2
      rw [h2val, hpval, hreal, mul_one]
      exact hsq
    · intro ℓ hℓ
      have hℓp : ℓ ≠ p := fun h => hℓ (by
        rw [h]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have hℓ2 : ℓ ≠ twoPrime := fun h => hℓ (by
        rw [h]
        exact Finset.mem_insert_self _ _)
      have h2 : (ℓ : ℕ) ≠ 2 := fun h => hℓ2 (Subtype.ext h)
      exact hilbertSym_padic_odd_units h2 (by norm_num)
        (by exact_mod_cast (Nat.Prime.ne_zero p.2))
        padic_valuation_neg_one (padic_valuation_prime_ne hℓp.symm)

-- Theorem: Hilbert reciprocity for the pair `(p,p)`.
theorem hilbertProd_prime_self (p : Nat.Primes) : hilbertProd (p : ℚ) (p : ℚ) = 1 := by
  by_cases hp2 : (p : ℕ) = 2
  · obtain rfl : p = twoPrime := Subtype.ext hp2
    unfold hilbertProd
    rw [finprod_hilbertSym_eq_finset_prod (S := {twoPrime}) ?_]
    · rw [Finset.prod_singleton]
      rw [show hilbertSym (((twoPrime : ℚ) : ℚ_[twoPrime]))
            (((twoPrime : ℚ) : ℚ_[twoPrime])) = 1 by
        exact hilbertSym_padic_two_two_two]
      rw [show hilbertSym (((twoPrime : ℚ) : ℝ)) (((twoPrime : ℚ) : ℝ)) = 1 by
        simpa using hilbertSym_real_pos_pos 2 2 (by norm_num) (by norm_num)]
      norm_num
    · intro ℓ hℓ
      have h2 : (ℓ : ℕ) ≠ 2 := fun h => hℓ (by
        rw [show ℓ = twoPrime from Subtype.ext h]
        exact Finset.mem_singleton_self _)
      exact hilbertSym_padic_odd_units h2 (prime_ratCast_ne_zero twoPrime ℓ)
        (prime_ratCast_ne_zero twoPrime ℓ)
        (padic_valuation_two_cast h2) (padic_valuation_two_cast h2)
  · have hne : twoPrime ≠ p := (prime_ne_twoPrime hp2).symm
    unfold hilbertProd
    rw [finprod_hilbertSym_eq_finset_prod (S := {twoPrime, p}) ?_]
    · rw [Finset.prod_insert (by simpa [Finset.mem_singleton] using hne),
        Finset.prod_singleton]
      have h2val : hilbertSym (((p : ℚ) : ℚ_[twoPrime])) (((p : ℚ) : ℚ_[twoPrime]))
          = legendreSym (p : ℕ) (-1) := by
        have h := hilbertSym_padic_two_unit_unit (p : ℕ) (not_two_dvd_of_ne_two hp2)
        rw [(legendreSym.at_neg_one hp2).symm] at h
        exact h
      have hpval : hilbertSym (((p : ℚ) : ℚ_[p])) (((p : ℚ) : ℚ_[p]))
          = legendreSym (p : ℕ) (-1) :=
        hilbertSym_padic_odd_prime_self p hp2
      have hreal : hilbertSym (((p : ℚ) : ℝ)) (((p : ℚ) : ℝ)) = 1 :=
        hilbertSym_real_pos_pos _ _ (prime_cast_pos p) (prime_cast_pos p)
      have hsq : legendreSym (p : ℕ) (-1) * legendreSym (p : ℕ) (-1) = 1 :=
        legendreSym_neg_one_sq p hp2
      rw [h2val, hpval, hreal, mul_one]
      exact hsq
    · intro ℓ hℓ
      have hℓp : ℓ ≠ p := fun h => hℓ (by
        rw [h]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have hℓ2 : ℓ ≠ twoPrime := fun h => hℓ (by
        rw [h]
        exact Finset.mem_insert_self _ _)
      have h2 : (ℓ : ℕ) ≠ 2 := fun h => hℓ2 (Subtype.ext h)
      exact hilbertSym_padic_odd_units h2 (prime_ratCast_ne_zero p ℓ)
        (prime_ratCast_ne_zero p ℓ)
        (padic_valuation_prime_ne hℓp.symm) (padic_valuation_prime_ne hℓp.symm)

/-! ### Phase 2, the case `(p,q)` of distinct primes

The final generator case is genuinely quadratic reciprocity.  At the two odd places `p` and
`q` the local symbols are `(q/p)` and `(p/q)`; at `2` the symbol is the quadratic-reciprocity
sign `(-1)^{(p-1)/2 · (q-1)/2}`; and the archimedean symbol is `1` because both primes are
positive.  The product is `1` by `legendreSym.quadratic_reciprocity`. -/

-- Theorem: `parityPow (-1) (omg (unitTwo n)) = χ₈ n` for odd `n`.
private lemma parityPow_omg_unitTwo (n : ℕ) (hn : ¬ 2 ∣ n) :
    parityPow (-1) (omg (unitTwo n hn)) = ZMod.χ₈ n := by
  have hn2 : n % 2 ≠ 0 := fun h => hn ((Nat.dvd_iff_mod_eq_zero).mpr h)
  have hm1 : (unitTwo n hn : ℤ_[2]).toZModPow 3 = 1 ↔ n % 8 = 1 := by
    rw [unitTwo_toZModPow_three, show (1 : ZMod 8) = ((1 : ℕ) : ZMod 8) by rfl,
      ZMod.natCast_eq_natCast_iff']
  have hm7 : (unitTwo n hn : ℤ_[2]).toZModPow 3 = 7 ↔ n % 8 = 7 := by
    rw [unitTwo_toZModPow_three, show (7 : ZMod 8) = ((7 : ℕ) : ZMod 8) by rfl,
      ZMod.natCast_eq_natCast_iff']
  by_cases h : (unitTwo n hn : ℤ_[2]).toZModPow 3 = 1
      ∨ (unitTwo n hn : ℤ_[2]).toZModPow 3 = 7
  · have hn8 : n % 8 = 1 ∨ n % 8 = 7 :=
      h.elim (fun a => Or.inl (hm1.mp a)) (fun b => Or.inr (hm7.mp b))
    rw [omg, ite_eq_left h, parityPow, ite_eq_left (show Even (0 : ℤ) by decide),
      ZMod.χ₈_nat_eq_if_mod_eight, ite_eq_right hn2, ite_eq_left hn8]
  · have hn8 : ¬ (n % 8 = 1 ∨ n % 8 = 7) := fun hc =>
      h (hc.elim (fun a => Or.inl (hm1.mpr a)) (fun b => Or.inr (hm7.mpr b)))
    rw [omg, ite_eq_right h, parityPow, ite_eq_right (show ¬ Even (1 : ℤ) by decide),
      ZMod.χ₈_nat_eq_if_mod_eight, ite_eq_right hn2, ite_eq_right hn8]

-- Theorem: `(2,n)_2 = χ₈ n` for odd `n`.
private lemma hilbertSym_padic_two_two_unit_nat (n : ℕ) (hn : ¬ 2 ∣ n) :
    hilbertSym (2 : ℚ_[2]) (((n : ℚ) : ℚ_[2])) = ZMod.χ₈ n := by
  have h := hilbertSym_two_unit_char (unitTwo n hn)
  rw [coe_unitTwo n hn] at h
  rw [h, parityPow_omg_unitTwo n hn]

-- Theorem: `(2,q)_q = (2/q)` for odd `q`.
private lemma hilbertSym_padic_odd_two_prime (q : Nat.Primes) (hq2 : (q : ℕ) ≠ 2) :
    hilbertSym (((2 : ℚ) : ℚ_[q])) (((q : ℚ) : ℚ_[q])) = legendreSym (q : ℕ) 2 := by
  have ha : (((2 : ℚ) : ℚ_[q])) ≠ 0 := Rat.cast_ne_zero.mpr (by norm_num)
  have hb : (((q : ℚ) : ℚ_[q])) ≠ 0 := prime_ratCast_ne_zero q (q : ℕ)
  have h2v : Padic.valuation (((2 : ℚ) : ℚ_[q])) = 0 :=
    padic_valuation_natCast_cast (ℓ := (q : ℕ)) (n := 2)
      (fun h => hq2 ((Nat.prime_dvd_prime_iff_eq q.2 Nat.prime_two).mp h))
  rw [hilbertSym_padic_odd_eq hq2 ha hb, h2v, padic_valuation_prime_self q]
  rw [zero_mul, parityPow_even' (show Even (0 : ℤ) by decide),
    parityPow_odd' (show ¬ Even (1 : ℤ) by decide),
    parityPow_even' (show Even (0 : ℤ) by decide)]
  simp only [one_mul, mul_one]
  exact quadraticChar_padicUnit_nat (ℓ := (q : ℕ)) (n := 2) (by norm_num)
    (fun h => hq2 ((Nat.prime_dvd_prime_iff_eq q.2 Nat.prime_two).mp h))

-- Theorem: `(p,q)_p = (q/p)` for distinct primes `p, q` with `p` odd.
private lemma hilbertSym_padic_odd_prime_prime (p q : Nat.Primes) (hpq : p ≠ q)
    (hp2 : (p : ℕ) ≠ 2) :
    hilbertSym (((p : ℚ) : ℚ_[p])) (((q : ℚ) : ℚ_[p])) = legendreSym (p : ℕ) (q : ℕ) := by
  have ha : (((p : ℚ) : ℚ_[p])) ≠ 0 := prime_ratCast_ne_zero p (p : ℕ)
  have hb : (((q : ℚ) : ℚ_[p])) ≠ 0 := prime_ratCast_ne_zero q (p : ℕ)
  have hpq_dvd : ¬ (p : ℕ) ∣ (q : ℕ) :=
    fun h => hpq (Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.2 q.2).mp h))
  rw [hilbertSym_padic_odd_eq hp2 ha hb, padic_valuation_prime_self p,
    padic_valuation_prime_ne hpq.symm]
  rw [mul_zero, parityPow_even' (show Even (0 : ℤ) by decide),
    parityPow_even' (show Even (0 : ℤ) by decide),
    parityPow_odd' (show ¬ Even (1 : ℤ) by decide)]
  simp only [one_mul, mul_one]
  exact quadraticChar_padicUnit_nat (ℓ := (p : ℕ)) (n := (q : ℕ)) (Nat.Prime.ne_zero q.2)
    hpq_dvd

-- Theorem: `(p,q)_2 = (-1)^{(p-1)/2 · (q-1)/2}` for distinct odd primes.
private lemma hilbertSym_padic_two_two_odd (p q : Nat.Primes) (hp2 : (p : ℕ) ≠ 2)
    (hq2 : (q : ℕ) ≠ 2) :
    hilbertSym (((p : ℚ) : ℚ_[2])) (((q : ℚ) : ℚ_[2]))
      = (-1 : ℤ) ^ ((p : ℕ) / 2 * ((q : ℕ) / 2)) := by
  have hp_nd : ¬ 2 ∣ (p : ℕ) := not_two_dvd_of_ne_two hp2
  have hq_nd : ¬ 2 ∣ (q : ℕ) := not_two_dvd_of_ne_two hq2
  have hm1 : ((p : ℕ) : ZMod 4) = 1 ↔ (p : ℕ) % 4 = 1 := by
    rw [show (1 : ZMod 4) = ((1 : ℕ) : ZMod 4) by rfl, ZMod.natCast_eq_natCast_iff']
  have hm2 : ((q : ℕ) : ZMod 4) = 1 ↔ (q : ℕ) % 4 = 1 := by
    rw [show (1 : ZMod 4) = ((1 : ℕ) : ZMod 4) by rfl, ZMod.natCast_eq_natCast_iff']
  have h := hilbertSym_padic_two_units (unitTwo (p : ℕ) hp_nd) (unitTwo (q : ℕ) hq_nd)
  rw [coe_unitTwo (p : ℕ) hp_nd, coe_unitTwo (q : ℕ) hq_nd,
    unitTwo_toZModPow_two (p : ℕ) hp_nd, unitTwo_toZModPow_two (q : ℕ) hq_nd] at h
  rw [h]
  have hp4 : (p : ℕ) % 4 = 1 ∨ (p : ℕ) % 4 = 3 := by omega
  have hq4 : (q : ℕ) % 4 = 1 ∨ (q : ℕ) % 4 = 3 := by omega
  rcases hp4 with hp1 | hp3 <;> rcases hq4 with hq1 | hq3
  · rw [ite_eq_left (Or.inl (hm1.mpr hp1)), pow_mul,
      ZMod.neg_one_pow_div_two_of_one_mod_four hp1, one_pow]
  · rw [ite_eq_left (Or.inl (hm1.mpr hp1)), pow_mul,
      ZMod.neg_one_pow_div_two_of_one_mod_four hp1, one_pow]
  · rw [ite_eq_left (Or.inr (hm2.mpr hq1)), pow_mul,
      ZMod.neg_one_pow_div_two_of_three_mod_four hp3,
      ZMod.neg_one_pow_div_two_of_one_mod_four hq1]
  · rw [ite_eq_right (by
        rintro (hh | hh)
        · exact absurd (hm1.mp hh) (by omega)
        · exact absurd (hm2.mp hh) (by omega)),
      pow_mul, ZMod.neg_one_pow_div_two_of_three_mod_four hp3,
      ZMod.neg_one_pow_div_two_of_three_mod_four hq3]

-- Theorem: Hilbert reciprocity for the pair `(2,q)`, `q` odd.
theorem hilbertProd_two_prime (q : Nat.Primes) (hq2 : (q : ℕ) ≠ 2) :
    hilbertProd (2 : ℚ) (q : ℚ) = 1 := by
  have hq_nd : ¬ 2 ∣ (q : ℕ) := not_two_dvd_of_ne_two hq2
  have hne : twoPrime ≠ q := (prime_ne_twoPrime hq2).symm
  unfold hilbertProd
  rw [finprod_hilbertSym_eq_finset_prod (S := {twoPrime, q}) ?_]
  · rw [Finset.prod_insert (by simpa [Finset.mem_singleton] using hne),
      Finset.prod_singleton]
    have h2val : hilbertSym (((2 : ℚ) : ℚ_[twoPrime])) (((q : ℚ) : ℚ_[twoPrime]))
        = ZMod.χ₈ (q : ℕ) := by
      simpa using hilbertSym_padic_two_two_unit_nat (q : ℕ) hq_nd
    have hqval : hilbertSym (((2 : ℚ) : ℚ_[q])) (((q : ℚ) : ℚ_[q]))
        = ZMod.χ₈ (q : ℕ) := by
      rw [hilbertSym_padic_odd_two_prime q hq2, legendreSym.at_two hq2]
    have hreal : hilbertSym (((2 : ℚ) : ℝ)) (((q : ℚ) : ℝ)) = 1 :=
      hilbertSym_real_pos_pos _ _ (by norm_num) (prime_cast_pos q)
    have hsq : ZMod.χ₈ (q : ℕ) * ZMod.χ₈ (q : ℕ) = 1 := by
      rw [ZMod.χ₈_nat_eq_if_mod_eight, ite_eq_right (by omega : ¬ (q : ℕ) % 2 = 0)]
      split_ifs <;> norm_num
    rw [h2val, hqval, hreal, mul_one]
    exact hsq
  · intro ℓ hℓ
    have hℓq : ℓ ≠ q := fun h => hℓ (by
      rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hℓ2 : ℓ ≠ twoPrime := fun h => hℓ (by
      rw [h]
      exact Finset.mem_insert_self _ _)
    have h2 : (ℓ : ℕ) ≠ 2 := fun h => hℓ2 (Subtype.ext h)
    exact hilbertSym_padic_odd_units h2 (Rat.cast_ne_zero.mpr (by norm_num))
      (prime_ratCast_ne_zero q ℓ)
      (padic_valuation_two_cast h2) (padic_valuation_prime_ne hℓq.symm)

-- Theorem: Hilbert reciprocity for the pair `(p,q)` of distinct primes.
theorem hilbertProd_prime_prime (p q : Nat.Primes) (hpq : p ≠ q) :
    hilbertProd (p : ℚ) (q : ℚ) = 1 := by
  by_cases hp2 : (p : ℕ) = 2
  · obtain rfl : p = twoPrime := Subtype.ext hp2
    have hq2 : (q : ℕ) ≠ 2 := fun h => hpq (Subtype.ext h).symm
    simpa using hilbertProd_two_prime q hq2
  · by_cases hq2 : (q : ℕ) = 2
    · obtain rfl : q = twoPrime := Subtype.ext hq2
      rw [hilbertProd_comm]
      simpa using hilbertProd_two_prime p hp2
    · have hne1 : twoPrime ≠ p := (prime_ne_twoPrime hp2).symm
      have hne2 : twoPrime ≠ q := (prime_ne_twoPrime hq2).symm
      unfold hilbertProd
      rw [finprod_hilbertSym_eq_finset_prod (S := {twoPrime, p, q}) ?_]
      · rw [Finset.prod_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hne1, hne2⟩),
          Finset.prod_insert (by simpa [Finset.mem_singleton] using hpq),
          Finset.prod_singleton]
        have h2val : hilbertSym (((p : ℚ) : ℚ_[twoPrime])) (((q : ℚ) : ℚ_[twoPrime]))
            = (-1 : ℤ) ^ ((p : ℕ) / 2 * ((q : ℕ) / 2)) :=
          hilbertSym_padic_two_two_odd p q hp2 hq2
        have hpval : hilbertSym (((p : ℚ) : ℚ_[p])) (((q : ℚ) : ℚ_[p]))
            = legendreSym (p : ℕ) (q : ℕ) :=
          hilbertSym_padic_odd_prime_prime p q hpq hp2
        have hqval : hilbertSym (((p : ℚ) : ℚ_[q])) (((q : ℚ) : ℚ_[q]))
            = legendreSym (q : ℕ) (p : ℕ) := by
          rw [hilbertSym_comm]
          exact hilbertSym_padic_odd_prime_prime q p hpq.symm hq2
        have hreal : hilbertSym (((p : ℚ) : ℝ)) (((q : ℚ) : ℝ)) = 1 :=
          hilbertSym_real_pos_pos _ _ (prime_cast_pos p) (prime_cast_pos q)
        rw [h2val, hpval, hqval, hreal, mul_one]
        have hkey : legendreSym (p : ℕ) (q : ℕ) * legendreSym (q : ℕ) (p : ℕ)
            = (-1 : ℤ) ^ ((p : ℕ) / 2 * ((q : ℕ) / 2)) := by
          rw [mul_comm]
          exact legendreSym.quadratic_reciprocity hp2 hq2 (fun h => hpq (Subtype.ext h))
        rw [hkey, ← pow_add]
        exact Even.neg_one_pow ⟨_, rfl⟩
      · intro ℓ hℓ
        have hℓp : ℓ ≠ p := fun h => hℓ (by
          rw [h]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
        have hℓq : ℓ ≠ q := fun h => hℓ (by
          rw [h]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
        have hℓ2 : ℓ ≠ twoPrime := fun h => hℓ (by
          rw [h]
          exact Finset.mem_insert_self _ _)
        have h2 : (ℓ : ℕ) ≠ 2 := fun h => hℓ2 (Subtype.ext h)
        exact hilbertSym_padic_odd_units h2 (prime_ratCast_ne_zero p ℓ)
          (prime_ratCast_ne_zero q ℓ)
          (padic_valuation_prime_ne hℓp.symm) (padic_valuation_prime_ne hℓq.symm)

/-! ### Hilbert reciprocity -/

-- Theorem: Hilbert reciprocity over `ℚ`: the product of the local Hilbert symbols over all
-- places is `1`.
theorem hilbertReciprocity : HilbertReciprocity :=
  hilbertReciprocity_of_generators (fun g h hg hh => by
    rcases hg with rfl | ⟨p, rfl⟩
    · rcases hh with rfl | ⟨q, rfl⟩
      · simpa using hilbertProd_neg_one_neg_one
      · exact hilbertProd_neg_one_prime q
    · rcases hh with rfl | ⟨q, rfl⟩
      · rw [hilbertProd_comm]; exact hilbertProd_neg_one_prime p
      · by_cases hpq : p = q
        · subst hpq; exact hilbertProd_prime_self p
        · exact hilbertProd_prime_prime p q hpq)

end HasseMinkowski
