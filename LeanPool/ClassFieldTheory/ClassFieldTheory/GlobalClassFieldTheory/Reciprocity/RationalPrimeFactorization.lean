/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Rational
/-!
# Prime factorization of a nonzero rational number

This file records the elementary rational factorization needed for the
principal-idele calculation over `ℚ`.  At a fixed rational prime `p`, removing
the `p`-power from `x : ℚˣ` leaves the sign of `x` times the finite product of
the powers of all primes different from `p`.

The last declarations package rational `p`-adic units as units of `ℤ_[p]` and
identify the reduction of a natural unit modulo `p ^ k`.
-/

open scoped BigOperators
noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open scoped Classical in
/-- The prime subtype supplies the primality instance used at this local factor. -/
local instance rationalPrimeFactorizationPrimeFact (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

attribute [local instance] rationalPrimeFactorizationPrimeFact

open scoped Classical in
/-- A finite set containing every prime occurring in the numerator or
denominator of `x`, as well as the distinguished prime `p`. -/
def rationalPrimeFactorizationSupport
    (x : ℚˣ) (p : Nat.Primes) : Finset ℕ :=
  (Finset.range
    (max (max (x : ℚ).num.natAbs (x : ℚ).den) p.1 + 1)).filter
      Nat.Prime

open scoped Classical in
theorem mem_rationalPrimeFactorizationSupport
    (x : ℚˣ) (p : Nat.Primes) :
    p.1 ∈ rationalPrimeFactorizationSupport x p := by
  rw [rationalPrimeFactorizationSupport, Finset.mem_filter,
    Finset.mem_range]
  exact
    ⟨Nat.lt_succ_of_le
        (le_max_right
          (max (x : ℚ).num.natAbs (x : ℚ).den) p.1),
      p.2⟩

open scoped Classical in
/-- The rational `p`-adic unit part of `x`: multiply `x` by the inverse of
its `p`-power. -/
def rationalPrimeUnit (x : ℚˣ) (p : Nat.Primes) : ℚˣ :=
  (Units.mk0 (p.1 : ℚ) (by exact_mod_cast p.2.ne_zero)) ^
      (-padicValRat p.1 (x : ℚ)) * x

open scoped Classical in
@[simp]
theorem rationalPrimeUnit_val (x : ℚˣ) (p : Nat.Primes) :
    (rationalPrimeUnit x p : ℚ) =
      (p.1 : ℚ) ^ (-padicValRat p.1 (x : ℚ)) * (x : ℚ) := by
  simp [rationalPrimeUnit]

open scoped Classical in
/-- Removing the `p`-power from a nonzero rational number leaves
`p`-adic valuation zero. -/
theorem padicValRat_rationalPrimeUnit
    (x : ℚˣ) (p : Nat.Primes) :
    padicValRat p.1 (rationalPrimeUnit x p : ℚ) = 0 := by
  have hp0 : (p.1 : ℚ) ≠ 0 := by
    exact_mod_cast p.2.ne_zero
  have hpow0 :
      (p.1 : ℚ) ^ (-padicValRat p.1 (x : ℚ)) ≠ 0 :=
    zpow_ne_zero _ hp0
  rw [rationalPrimeUnit_val,
    padicValRat.mul hpow0 x.ne_zero,
    padicValRat.zpow,
    padicValRat.self p.2.one_lt]
  ring

open scoped Classical in
/-- The ordinary prime factorization of a nonzero rational number, over the
finite support chosen by `rationalPrimeFactorizationSupport`. -/
theorem rational_factorization_over_support
    (x : ℚˣ) (p : Nat.Primes) :
    (x : ℚ) =
      (((x : ℚ).num.sign : ℤ) : ℚ) *
        ∏ q ∈ rationalPrimeFactorizationSupport x p,
          (q : ℚ) ^ padicValRat q (x : ℚ) := by
  let r : ℚ := x
  let B : ℕ := max (max r.num.natAbs r.den) p.1 + 1
  let s : Finset ℕ := (Finset.range B).filter Nat.Prime
  have hsupport :
      rationalPrimeFactorizationSupport x p = s := by
    rfl
  have hnum0 : r.num.natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr
      (Rat.num_ne_zero.mpr x.ne_zero)
  have hden0 : r.den ≠ 0 :=
    r.den_ne_zero
  have hnum_lt : r.num.natAbs < B := by
    exact
      Nat.lt_succ_of_le
        (le_trans
          (le_max_left r.num.natAbs r.den)
          (le_max_left (max r.num.natAbs r.den) p.1))
  have hden_lt : r.den < B := by
    exact
      Nat.lt_succ_of_le
        (le_trans
          (le_max_right r.num.natAbs r.den)
          (le_max_left (max r.num.natAbs r.den) p.1))
  have hnumNat :=
    Nat.prod_pow_prime_padicValNat
      r.num.natAbs hnum0 B hnum_lt
  have hdenNat :=
    Nat.prod_pow_prime_padicValNat
      r.den hden0 B hden_lt
  have hnum :
      (∏ q ∈ s,
        (q : ℚ) ^ padicValNat q r.num.natAbs) =
          (r.num.natAbs : ℚ) := by
    norm_cast
  have hden :
      (∏ q ∈ s,
        (q : ℚ) ^ padicValNat q r.den) =
          (r.den : ℚ) := by
    norm_cast
  have hsign :
      (r.num : ℚ) =
        (((r.num.sign : ℤ) : ℚ)) * (r.num.natAbs : ℚ) := by
    have hsignInt :
        r.num.sign * (r.num.natAbs : ℤ) = r.num :=
      Int.sign_mul_natAbs r.num
    calc
      (r.num : ℚ) =
          ((r.num.sign * (r.num.natAbs : ℤ) : ℤ) : ℚ) :=
        congrArg (fun z : ℤ => (z : ℚ)) hsignInt.symm
      _ =
          (((r.num.sign : ℤ) : ℚ)) * (r.num.natAbs : ℚ) := by
        norm_num
  have hprod :
      (∏ q ∈ s, (q : ℚ) ^ padicValRat q r) =
        (r.num.natAbs : ℚ) / (r.den : ℚ) := by
    calc
      (∏ q ∈ s, (q : ℚ) ^ padicValRat q r) =
          ∏ q ∈ s,
            (q : ℚ) ^ padicValNat q r.num.natAbs /
              (q : ℚ) ^ padicValNat q r.den := by
        apply Finset.prod_congr rfl
        intro q hq
        have hqprime : q.Prime :=
          (Finset.mem_filter.mp hq).2
        rw [padicValRat_def, padicValInt,
          zpow_sub₀ (by exact_mod_cast hqprime.ne_zero),
          zpow_natCast, zpow_natCast]
      _ =
          (∏ q ∈ s,
              (q : ℚ) ^ padicValNat q r.num.natAbs) /
            ∏ q ∈ s,
              (q : ℚ) ^ padicValNat q r.den := by
        rw [Finset.prod_div_distrib]
      _ = (r.num.natAbs : ℚ) / (r.den : ℚ) := by
        rw [hnum, hden]
  rw [hsupport]
  calc
    (x : ℚ) = (r.num : ℚ) / (r.den : ℚ) := by
      simpa only [r] using r.num_div_den.symm
    _ =
        (((r.num.sign : ℤ) : ℚ)) *
          ((r.num.natAbs : ℚ) / (r.den : ℚ)) := by
      rw [hsign, mul_div_assoc]
    _ =
        (((r.num.sign : ℤ) : ℚ)) *
          ∏ q ∈ s, (q : ℚ) ^ padicValRat q r := by
      rw [hprod]
    _ =
        ((((x : ℚ).num.sign : ℤ) : ℚ)) *
          ∏ q ∈ s, (q : ℚ) ^ padicValRat q (x : ℚ) := by
      rfl

open scoped Classical in
/-- The `p`-adic unit part of `x` is its sign times the finite product of
`q ^ padicValRat q x` over the primes `q ≠ p`. -/
theorem rationalPrimeUnit_factorization
    (x : ℚˣ) (p : Nat.Primes) :
    (rationalPrimeUnit x p : ℚ) =
      (((x : ℚ).num.sign : ℤ) : ℚ) *
        ∏ q ∈ (rationalPrimeFactorizationSupport x p).erase p.1,
          (q : ℚ) ^ padicValRat q (x : ℚ) := by
  let s := rationalPrimeFactorizationSupport x p
  let f : ℕ → ℚ :=
    fun q => (q : ℚ) ^ padicValRat q (x : ℚ)
  have hp_mem : p.1 ∈ s :=
    mem_rationalPrimeFactorizationSupport x p
  have hsplit :
      f p.1 * ∏ q ∈ s.erase p.1, f q =
        ∏ q ∈ s, f q :=
    Finset.mul_prod_erase s f hp_mem
  have hfactor :
      (x : ℚ) =
        (((x : ℚ).num.sign : ℤ) : ℚ) *
          ∏ q ∈ s, f q := by
    simpa only [s, f] using
      rational_factorization_over_support x p
  have hp0 : (p.1 : ℚ) ≠ 0 := by
    exact_mod_cast p.2.ne_zero
  rw [rationalPrimeUnit_val]
  calc
    (p.1 : ℚ) ^ (-padicValRat p.1 (x : ℚ)) * (x : ℚ) =
        (p.1 : ℚ) ^ (-padicValRat p.1 (x : ℚ)) *
          ((((x : ℚ).num.sign : ℤ) : ℚ) *
            ∏ q ∈ s, f q) :=
      congrArg
        (fun y : ℚ =>
          (p.1 : ℚ) ^ (-padicValRat p.1 (x : ℚ)) * y)
        hfactor
    _ =
        (p.1 : ℚ) ^ (-padicValRat p.1 (x : ℚ)) *
          ((((x : ℚ).num.sign : ℤ) : ℚ) *
            (f p.1 * ∏ q ∈ s.erase p.1, f q)) := by
      rw [hsplit]
    _ =
        (((x : ℚ).num.sign : ℤ) : ℚ) *
          (((p.1 : ℚ) ^ (-padicValRat p.1 (x : ℚ)) *
              (p.1 : ℚ) ^ padicValRat p.1 (x : ℚ)) *
            ∏ q ∈ s.erase p.1, f q) := by
      dsimp only [f]
      ring
    _ =
        (((x : ℚ).num.sign : ℤ) : ℚ) *
          ∏ q ∈ s.erase p.1, f q := by
      rw [← zpow_add₀ hp0, neg_add_cancel, zpow_zero, one_mul]
    _ =
        (((x : ℚ).num.sign : ℤ) : ℚ) *
          ∏ q ∈
              (rationalPrimeFactorizationSupport x p).erase p.1,
            (q : ℚ) ^ padicValRat q (x : ℚ) := by
      rfl

open scoped Classical in
/-- A nonzero rational number of `p`-adic valuation zero, regarded as a
unit of the `p`-adic integers. -/
def padicIntUnitOfRat
    (p : Nat.Primes) (y : ℚ)
    (hy : y ≠ 0) (hval : padicValRat p.1 y = 0) :
    ℤ_[p.1]ˣ :=
  PadicInt.mkUnits (u := (y : ℚ_[p.1])) (by
    rw [Padic.eq_padicNorm,
      padicNorm.eq_zpow_of_nonzero hy, hval]
    simp)

open scoped Classical in
/-- The underlying `p`-adic number of `padicIntUnitOfRat` is the original
rational number. -/
@[simp]
theorem padicIntUnitOfRat_coe
    (p : Nat.Primes) (y : ℚ)
    (hy : y ≠ 0) (hval : padicValRat p.1 y = 0) :
    (((padicIntUnitOfRat p y hy hval : ℤ_[p.1]) : ℚ_[p.1])) =
      (y : ℚ_[p.1]) := by
  exact PadicInt.mkUnits_eq _

open scoped Classical in
/-- The sign of a nonzero rational numerator is a unit at every finite
prime. -/
theorem padicValRat_rational_num_sign
    (x : ℚˣ) (p : Nat.Primes) :
    padicValRat p.1 ((((x : ℚ).num.sign : ℤ) : ℚ)) = 0 := by
  have hnum : (x : ℚ).num ≠ 0 :=
    Rat.num_ne_zero.mpr x.ne_zero
  rcases lt_or_gt_of_ne hnum with hneg | hpos
  · have hsign : (x : ℚ).num.sign = -1 := by
      rw [Int.sign_eq_sign, sign_neg hneg]
      rfl
    rw [hsign]
    simp
  · have hsign : (x : ℚ).num.sign = 1 := by
      rw [Int.sign_eq_sign, sign_pos hpos]
      rfl
    rw [hsign]
    simp

open scoped Classical in
/-- The actual sign of `x`, regarded as a unit of the `p`-adic integers. -/
def rationalSignPadicUnit
    (x : ℚˣ) (p : Nat.Primes) : ℤ_[p.1]ˣ :=
  padicIntUnitOfRat p ((((x : ℚ).num.sign : ℤ) : ℚ))
    (by
      exact_mod_cast
        (Int.sign_eq_zero_iff_zero.not.mpr
          (Rat.num_ne_zero.mpr x.ne_zero)))
    (padicValRat_rational_num_sign x p)

open scoped Classical in
/-- The underlying `p`-adic number of `rationalSignPadicUnit` is the sign of
the rational numerator. -/
theorem rationalSignPadicUnit_coe
    (x : ℚˣ) (p : Nat.Primes) :
    (((rationalSignPadicUnit x p : ℤ_[p.1]) : ℚ_[p.1])) =
      (((((x : ℚ).num.sign : ℤ) : ℚ) : ℚ_[p.1])) := by
  exact padicIntUnitOfRat_coe _ _ _ _

open scoped Classical in
/-- The value in `ℤ_[p]` of `rationalSignPadicUnit` is the integer sign. -/
@[simp]
theorem rationalSignPadicUnit_val
    (x : ℚˣ) (p : Nat.Primes) :
    (rationalSignPadicUnit x p : ℤ_[p.1]) =
      ((x : ℚ).num.sign : ℤ) := by
  apply Subtype.ext
  simp only [rationalSignPadicUnit_coe, PadicInt.coe_intCast,
    Rat.cast_intCast]

open scoped Classical in
/-- The rational sign unit has square one. -/
@[simp]
theorem rationalSignPadicUnit_sq
    (x : ℚˣ) (p : Nat.Primes) :
    rationalSignPadicUnit x p ^ 2 = 1 := by
  apply Units.ext
  change (rationalSignPadicUnit x p : ℤ_[p.1]) ^ 2 = 1
  rw [rationalSignPadicUnit_val]
  have hnum : (x : ℚ).num ≠ 0 :=
    Rat.num_ne_zero.mpr x.ne_zero
  rcases lt_or_gt_of_ne hnum with hneg | hpos
  · have hsign : (x : ℚ).num.sign = -1 := by
      rw [Int.sign_eq_sign, sign_neg hneg]
      rfl
    rw [hsign]
    simp
  · have hsign : (x : ℚ).num.sign = 1 := by
      rw [Int.sign_eq_sign, sign_pos hpos]
      rfl
    rw [hsign]
    simp

open scoped Classical in
/-- Reduction of the rational sign unit modulo `p ^ k` has the expected
integer value. -/
theorem rationalSignPadicUnit_toZModPow_val
    (x : ℚˣ) (p : Nat.Primes) (k : ℕ) :
    ((Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalSignPadicUnit x p) :
          (ZMod (p.1 ^ k))ˣ) : ZMod (p.1 ^ k)) =
      ((x : ℚ).num.sign : ℤ) := by
  change
    PadicInt.toZModPow k
        (rationalSignPadicUnit x p : ℤ_[p.1]) =
      ((x : ℚ).num.sign : ℤ)
  rw [rationalSignPadicUnit_val]
  simp

open scoped Classical in
/-- Reduction of the rational sign unit still has square one. -/
theorem rationalSignPadicUnit_toZModPow_sq
    (x : ℚˣ) (p : Nat.Primes) (k : ℕ) :
    Units.map (PadicInt.toZModPow k).toMonoidHom
          (rationalSignPadicUnit x p) ^ 2 =
      1 := by
  rw [← map_pow, rationalSignPadicUnit_sq, map_one]

open scoped Classical in
/-- A natural number prime to `p`, regarded as a unit of `ℤ_[p]`. -/
def padicNatUnit
    (p : Nat.Primes) (q : ℕ) (h : p.1.Coprime q) :
    ℤ_[p.1]ˣ :=
  PadicInt.mkUnits
    (u := (((q : ℤ_[p.1]) : ℚ_[p.1])))
    (by
      simpa using
        (PadicInt.norm_natCast_eq_one_iff (p := p.1)).2 h)

open scoped Classical in
@[simp]
theorem padicNatUnit_val
    (p : Nat.Primes) (q : ℕ) (h : p.1.Coprime q) :
    (padicNatUnit p q h : ℤ_[p.1]) = q := by
  apply Subtype.ext
  rfl

open scoped Classical in
/-- Reducing the canonical `p`-adic unit attached to `q` modulo `p ^ k`
gives the canonical unit represented by `q` in `ZMod (p ^ k)`. -/
theorem padicNatUnit_toZModPow
    (p : Nat.Primes) (q k : ℕ) (h : p.1.Coprime q) :
    Units.map (PadicInt.toZModPow k).toMonoidHom
        (padicNatUnit p q h) =
      ZMod.unitOfCoprime q (h.symm.pow_right k) := by
  apply Units.ext
  simp

open scoped Classical in
/-- The successor of `p` is a `p`-adic unit. -/
theorem padicValRat_rationalPrime_succ
    (p : Nat.Primes) :
    padicValRat p.1 (((p.1 + 1 : ℕ) : ℚ)) = 0 := by
  have hnot :
      ¬ p.1 ∣ p.1 + 1 :=
    p.2.coprime_iff_not_dvd.mp
      (Nat.coprime_self_add_right.mpr
        (Nat.coprime_one_right p.1))
  rw [padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd hnot]
  norm_num

open scoped Classical in
/-- A positive natural number greater than one, prime to `p`, gives a
genuine non-torsion unit of `ℤ_[p]`. -/
theorem padicNatUnit_not_isOfFinOrder_of_one_lt
    (p : Nat.Primes) (n : ℕ)
    (hcoprime : p.1.Coprime n)
    (hn : 1 < n) :
    ¬ IsOfFinOrder (padicNatUnit p n hcoprime) := by
  intro hfinite
  obtain ⟨k, hk, hpow⟩ :=
    isOfFinOrder_iff_pow_eq_one.mp hfinite
  have hval :=
    congrArg
      (fun z : ℤ_[p.1]ˣ => (z : ℤ_[p.1]))
      hpow
  have hnat : n ^ k = 1 := by
    rw [Units.val_pow_eq_pow_val,
      padicNatUnit_val] at hval
    simp at hval
    apply Nat.cast_injective (R := ℤ_[p.1])
    simpa only [Nat.cast_pow, Nat.cast_one] using hval
  exact
    (Nat.ne_of_gt
      (Nat.one_lt_pow hk.ne' hn)) hnat

open scoped Classical in
/-- Every member of the rational factorization support is prime. -/
theorem prime_of_mem_rationalPrimeFactorizationSupport
    (x : ℚˣ) (p : Nat.Primes) {q : ℕ}
    (hq : q ∈ rationalPrimeFactorizationSupport x p) :
    q.Prime :=
  (Finset.mem_filter.mp hq).2

open scoped Classical in
/-- The canonical embedding of the natural-number factorization support
into the type of natural primes. -/
def rationalPrimeFactorizationSupportEmbedding
    (x : ℚˣ) (p : Nat.Primes) :
    ↥(rationalPrimeFactorizationSupport x p) ↪ Nat.Primes where
  toFun q :=
    ⟨q.1,
      prime_of_mem_rationalPrimeFactorizationSupport
        x p q.2⟩
  inj' q r h := by
    apply Subtype.ext
    exact
      congrArg (fun z : Nat.Primes => (z : ℕ)) h

open scoped Classical in
/-- The factorization support as an actual finite set of `Nat.Primes`. -/
def rationalPrimeFactorizationPrimeSupport
    (x : ℚˣ) (p : Nat.Primes) : Finset Nat.Primes :=
  Finset.univ.map
    (rationalPrimeFactorizationSupportEmbedding x p)

open scoped Classical in
/-- Membership in the prime-valued support is exactly membership of the
underlying natural number in the original support. -/
@[simp]
theorem mem_rationalPrimeFactorizationPrimeSupport_iff
    (x : ℚˣ) (p : Nat.Primes) (q : Nat.Primes) :
    q ∈ rationalPrimeFactorizationPrimeSupport x p ↔
      q.1 ∈ rationalPrimeFactorizationSupport x p := by
  constructor
  · intro hq
    obtain ⟨r, -, hr⟩ :=
      Finset.mem_map.mp hq
    rw [← hr]
    exact r.2
  · intro hq
    apply Finset.mem_map.mpr
    refine
      ⟨⟨q.1, hq⟩,
        Finset.mem_univ _,
        ?_⟩
    apply Subtype.ext
    rfl

open scoped Classical in
/-- The distinguished prime belongs to the prime-valued support. -/
theorem mem_rationalPrimeFactorizationPrimeSupport
    (x : ℚˣ) (p : Nat.Primes) :
    p ∈ rationalPrimeFactorizationPrimeSupport x p :=
  (mem_rationalPrimeFactorizationPrimeSupport_iff x p p).2
    (mem_rationalPrimeFactorizationSupport x p)

open scoped Classical in
/-- Erasing `p` commutes with passing from natural-number support to
prime-valued support. -/
theorem mem_rationalPrimeFactorizationPrimeSupport_erase_iff
    (x : ℚˣ) (p q : Nat.Primes) :
    q ∈ (rationalPrimeFactorizationPrimeSupport x p).erase p ↔
      q.1 ∈ (rationalPrimeFactorizationSupport x p).erase p.1 := by
  rw [Finset.mem_erase, Finset.mem_erase]
  constructor
  · rintro ⟨hqp, hq⟩
    exact
      ⟨fun hval => hqp (Subtype.ext hval),
        (mem_rationalPrimeFactorizationPrimeSupport_iff
          x p q).1 hq⟩
  · rintro ⟨hval, hq⟩
    exact
      ⟨fun hqp => hval (congrArg Subtype.val hqp),
        (mem_rationalPrimeFactorizationPrimeSupport_iff
          x p q).2 hq⟩

open scoped Classical in
/-- The canonical prime associated with an element of the erased natural
support. -/
def rationalPrimeOfMemFactorizationSupportErase
    (x : ℚˣ) (p : Nat.Primes)
    (q : ↥((rationalPrimeFactorizationSupport x p).erase p.1)) :
    Nat.Primes :=
  ⟨q.1,
    prime_of_mem_rationalPrimeFactorizationSupport
      x p (Finset.mem_of_mem_erase q.2)⟩

open scoped Classical in
/-- The erased natural support and the erased prime-valued support have
canonically equivalent element types. -/
def rationalPrimeFactorizationSupportEraseEquiv
    (x : ℚˣ) (p : Nat.Primes) :
    ↥((rationalPrimeFactorizationSupport x p).erase p.1) ≃
      ↥((rationalPrimeFactorizationPrimeSupport x p).erase p) where
  toFun q :=
    ⟨rationalPrimeOfMemFactorizationSupportErase x p q,
      (mem_rationalPrimeFactorizationPrimeSupport_erase_iff
        x p _).2 q.2⟩
  invFun q :=
    ⟨q.1.1,
      (mem_rationalPrimeFactorizationPrimeSupport_erase_iff
        x p q.1).1 q.2⟩
  left_inv q := by
    apply Subtype.ext
    rfl
  right_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

open scoped Classical in
/-- A prime in the support with `p` erased is coprime to `p`. -/
theorem coprime_of_mem_rationalPrimeFactorizationSupport_erase
    (x : ℚˣ) (p : Nat.Primes) {q : ℕ}
    (hq :
      q ∈ (rationalPrimeFactorizationSupport x p).erase p.1) :
    p.1.Coprime q := by
  have hqprime :
      q.Prime :=
    prime_of_mem_rationalPrimeFactorizationSupport x p
      (Finset.mem_of_mem_erase hq)
  exact
    (Nat.coprime_primes p.2 hqprime).2
      (Finset.ne_of_mem_erase hq).symm

open scoped Classical in
/-- The rational prime-unit factorization, lifted from `ℚ` to an exact
identity of units of `ℤ_[p]`. -/
theorem padicIntUnitOfRat_rationalPrimeUnit_factorization
    (x : ℚˣ) (p : Nat.Primes) :
    padicIntUnitOfRat p (rationalPrimeUnit x p : ℚ)
        (rationalPrimeUnit x p).ne_zero
        (padicValRat_rationalPrimeUnit x p) =
      rationalSignPadicUnit x p *
        ∏ q :
            ↥((rationalPrimeFactorizationSupport x p).erase p.1),
          (padicNatUnit p q.1
              (coprime_of_mem_rationalPrimeFactorizationSupport_erase
                x p q.2)) ^
            padicValRat q.1 (x : ℚ) := by
  let : Fact p.1.Prime := ⟨p.2⟩
  have hQ :=
    congrArg (algebraMap ℚ ℚ_[p.1])
      (rationalPrimeUnit_factorization x p)
  let ι := PadicInt.Coe.ringHom (p := p.1)
  have hι_apply (z : ℤ_[p.1]) :
      ι z = (z : ℚ_[p.1]) := rfl
  have hι : Function.Injective ι :=
    fun _ _ h => PadicInt.ext h
  have hprod :
      (∏ q :
          ↥((rationalPrimeFactorizationSupport x p).erase p.1),
        ι
          (((padicNatUnit p q.1
                (coprime_of_mem_rationalPrimeFactorizationSupport_erase
                  x p q.2)) ^
              padicValRat q.1 (x : ℚ) : ℤ_[p.1]ˣ) : ℤ_[p.1])) =
        ∏ q ∈ (rationalPrimeFactorizationSupport x p).erase p.1,
          (q : ℚ_[p.1]) ^ padicValRat q (x : ℚ) := by
    calc
      _ =
          ∏ q :
              ↥((rationalPrimeFactorizationSupport x p).erase p.1),
            (q.1 : ℚ_[p.1]) ^ padicValRat q.1 (x : ℚ) := by
        apply Finset.prod_congr rfl
        intro q _
        let u : ℤ_[p.1]ˣ :=
          padicNatUnit p q.1
            (coprime_of_mem_rationalPrimeFactorizationSupport_erase
              x p q.2)
        let n : ℤ := padicValRat q.1 (x : ℚ)
        have hu : (u : ℤ_[p.1]) = q.1 := by
          dsimp only [u]
          exact
            padicNatUnit_val p q.1
              (coprime_of_mem_rationalPrimeFactorizationSupport_erase
                x p q.2)
        have huQ : ((u : ℤ_[p.1]) : ℚ_[p.1]) = (q.1 : ℚ_[p.1]) := by
          simpa only [PadicInt.coe_natCast] using
            congrArg (fun z : ℤ_[p.1] => (z : ℚ_[p.1])) hu
        let U : ℤ_[p.1]ˣ →* ℚ_[p.1]ˣ :=
          Units.map ι.toMonoidHom
        have hUQ : ((U u : ℚ_[p.1]ˣ) : ℚ_[p.1]) =
            (q.1 : ℚ_[p.1]) := by
          change ι (u : ℤ_[p.1]) = (q.1 : ℚ_[p.1])
          simpa only [hι_apply] using huQ
        change
          ((((u ^ n : ℤ_[p.1]ˣ) : ℤ_[p.1]) : ℚ_[p.1])) =
            (q.1 : ℚ_[p.1]) ^ n
        calc
          _ = ((U (u ^ n) : ℚ_[p.1]ˣ) : ℚ_[p.1]) := rfl
          _ = (((U u) ^ n : ℚ_[p.1]ˣ) : ℚ_[p.1]) :=
            congrArg (fun v : ℚ_[p.1]ˣ => (v : ℚ_[p.1]))
              (map_zpow U u n)
          _ = ((U u : ℚ_[p.1]ˣ) : ℚ_[p.1]) ^ n :=
            Units.val_zpow_eq_zpow_val (U u) n
          _ = _ := congrArg (fun z : ℚ_[p.1] => z ^ n) hUQ
      _ = _ :=
        Finset.prod_coe_sort
          ((rationalPrimeFactorizationSupport x p).erase p.1)
          (fun q : ℕ =>
            (q : ℚ_[p.1]) ^ padicValRat q (x : ℚ))
  apply Units.ext
  apply hι
  rw [Units.val_mul, Units.coe_prod]
  change
    ι
        (padicIntUnitOfRat p (rationalPrimeUnit x p : ℚ)
          (rationalPrimeUnit x p).ne_zero
          (padicValRat_rationalPrimeUnit x p) : ℤ_[p.1]) =
      ι
        ((rationalSignPadicUnit x p : ℤ_[p.1]) *
          ∏ q :
              ↥((rationalPrimeFactorizationSupport x p).erase p.1),
            (((padicNatUnit p q.1
                (coprime_of_mem_rationalPrimeFactorizationSupport_erase
                  x p q.2)) ^
              padicValRat q.1 (x : ℚ) : ℤ_[p.1]ˣ) : ℤ_[p.1]))
  rw [map_mul, map_prod]
  rw [hprod]
  simp only [hι_apply, padicIntUnitOfRat_coe,
    rationalSignPadicUnit_coe]
  change
    (algebraMap ℚ ℚ_[p.1]) (rationalPrimeUnit x p : ℚ) =
      (algebraMap ℚ ℚ_[p.1])
          (((x : ℚ).num.sign : ℤ) : ℚ) *
        ∏ q ∈ (rationalPrimeFactorizationSupport x p).erase p.1,
          (q : ℚ_[p.1]) ^ padicValRat q (x : ℚ)
  simpa only [map_mul, map_prod, map_zpow₀,
    map_natCast] using hQ

open scoped Classical in
/-- The rational prime-unit factorization after reduction modulo `p ^ k`. -/
theorem padicIntUnitOfRat_rationalPrimeUnit_toZModPow
    (x : ℚˣ) (p : Nat.Primes) (k : ℕ) :
    Units.map (PadicInt.toZModPow k).toMonoidHom
        (padicIntUnitOfRat p (rationalPrimeUnit x p : ℚ)
          (rationalPrimeUnit x p).ne_zero
          (padicValRat_rationalPrimeUnit x p)) =
      Units.map (PadicInt.toZModPow k).toMonoidHom
          (rationalSignPadicUnit x p) *
        ∏ q :
            ↥((rationalPrimeFactorizationSupport x p).erase p.1),
          (ZMod.unitOfCoprime q.1
              ((coprime_of_mem_rationalPrimeFactorizationSupport_erase
                x p q.2).symm.pow_right k)) ^
            padicValRat q.1 (x : ℚ) := by
  have h :=
    congrArg
      (Units.map (PadicInt.toZModPow k).toMonoidHom)
      (padicIntUnitOfRat_rationalPrimeUnit_factorization x p)
  simpa only [map_mul, map_prod, map_zpow,
    padicNatUnit_toZModPow] using h

open scoped Classical in
/-- Multiplying the reduced rational prime-unit by the inverse powers of all
prime factors away from `p` recovers the reduced sign. -/
theorem padicIntUnitOfRat_rationalPrimeUnit_mul_inverseFactors_toZModPow
    (x : ℚˣ) (p : Nat.Primes) (k : ℕ) :
    Units.map (PadicInt.toZModPow k).toMonoidHom
          (padicIntUnitOfRat p (rationalPrimeUnit x p : ℚ)
            (rationalPrimeUnit x p).ne_zero
            (padicValRat_rationalPrimeUnit x p)) *
        ∏ q :
            ↥((rationalPrimeFactorizationSupport x p).erase p.1),
          (ZMod.unitOfCoprime q.1
              ((coprime_of_mem_rationalPrimeFactorizationSupport_erase
                x p q.2).symm.pow_right k)) ^
            (-padicValRat q.1 (x : ℚ)) =
      Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalSignPadicUnit x p) := by
  rw [padicIntUnitOfRat_rationalPrimeUnit_toZModPow]
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  simp

open scoped Classical in
/-- Prime-valued support form of the reduced rational product formula.
The direct `p`-adic unit factor times all inverse away-from-`p` factors
is the reduced rational sign. -/
theorem
    padicIntUnitOfRat_rationalPrimeUnit_mul_primeSupportInverseFactors_toZModPow
    (x : ℚˣ) (p : Nat.Primes) (k : ℕ) :
    Units.map (PadicInt.toZModPow k).toMonoidHom
          (padicIntUnitOfRat p (rationalPrimeUnit x p : ℚ)
            (rationalPrimeUnit x p).ne_zero
            (padicValRat_rationalPrimeUnit x p)) *
        ∏ q :
            ↥((rationalPrimeFactorizationPrimeSupport x p).erase p),
          (ZMod.unitOfCoprime q.1.1
              ((coprime_of_mem_rationalPrimeFactorizationSupport_erase
                x p
                ((mem_rationalPrimeFactorizationPrimeSupport_erase_iff
                  x p q.1).1 q.2)).symm.pow_right k)) ^
            (-padicValRat q.1.1 (x : ℚ)) =
      Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalSignPadicUnit x p) := by
  have hprod :
      (∏ q :
          ↥((rationalPrimeFactorizationPrimeSupport x p).erase p),
        (ZMod.unitOfCoprime q.1.1
            ((coprime_of_mem_rationalPrimeFactorizationSupport_erase
              x p
              ((mem_rationalPrimeFactorizationPrimeSupport_erase_iff
                x p q.1).1 q.2)).symm.pow_right k)) ^
          (-padicValRat q.1.1 (x : ℚ))) =
        ∏ q :
            ↥((rationalPrimeFactorizationSupport x p).erase p.1),
          (ZMod.unitOfCoprime q.1
              ((coprime_of_mem_rationalPrimeFactorizationSupport_erase
                x p q.2).symm.pow_right k)) ^
            (-padicValRat q.1 (x : ℚ)) := by
    refine
      Fintype.prod_equiv
        (rationalPrimeFactorizationSupportEraseEquiv x p).symm
        _ _ ?_
    intro q
    rfl
  rw [hprod]
  exact
    padicIntUnitOfRat_rationalPrimeUnit_mul_inverseFactors_toZModPow
      x p k

open scoped Classical in
/-- Multiplication by the reduced sign cancels the sign in the reduced
prime-unit factorization. -/
theorem rationalSignPadicUnit_mul_primeUnit_toZModPow
    (x : ℚˣ) (p : Nat.Primes) (k : ℕ) :
    Units.map (PadicInt.toZModPow k).toMonoidHom
          (rationalSignPadicUnit x p) *
        Units.map (PadicInt.toZModPow k).toMonoidHom
          (padicIntUnitOfRat p (rationalPrimeUnit x p : ℚ)
            (rationalPrimeUnit x p).ne_zero
            (padicValRat_rationalPrimeUnit x p)) =
      ∏ q :
          ↥((rationalPrimeFactorizationSupport x p).erase p.1),
        (ZMod.unitOfCoprime q.1
            ((coprime_of_mem_rationalPrimeFactorizationSupport_erase
              x p q.2).symm.pow_right k)) ^
          padicValRat q.1 (x : ℚ) := by
  rw [padicIntUnitOfRat_rationalPrimeUnit_toZModPow]
  rw [← mul_assoc, ← pow_two,
    rationalSignPadicUnit_toZModPow_sq, one_mul]

open scoped Classical in
/-- Inverse/cancellation form of the reduced prime-unit factorization. -/
theorem padicIntUnitOfRat_rationalPrimeUnit_toZModPow_inv_mul
    (x : ℚˣ) (p : Nat.Primes) (k : ℕ) :
    (Units.map (PadicInt.toZModPow k).toMonoidHom
        (padicIntUnitOfRat p (rationalPrimeUnit x p : ℚ)
          (rationalPrimeUnit x p).ne_zero
          (padicValRat_rationalPrimeUnit x p)))⁻¹ *
      (Units.map (PadicInt.toZModPow k).toMonoidHom
          (rationalSignPadicUnit x p) *
        ∏ q :
            ↥((rationalPrimeFactorizationSupport x p).erase p.1),
          (ZMod.unitOfCoprime q.1
              ((coprime_of_mem_rationalPrimeFactorizationSupport_erase
                x p q.2).symm.pow_right k)) ^
            padicValRat q.1 (x : ℚ)) =
      1 := by
  rw [← padicIntUnitOfRat_rationalPrimeUnit_toZModPow]
  simp

end Reciprocity
end GlobalClassFieldTheory
