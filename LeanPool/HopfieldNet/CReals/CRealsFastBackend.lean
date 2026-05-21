/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.CRealAQBackendEquiv
import LeanPool.HopfieldNet.CReals.CRealsFast
import Mathlib.Tactic

/-!
This file integrates the executable dyadic engine in `Computable.Fast` with the existing
`ApproxRationals`/`CRealRep`/`CRealAQ` proof stack.

The key deliverable is an `ApproxRationals` instance for `Computable.Fast.Dyadic`.
-/

namespace Computable.Fast
namespace Dyadic

@[simp] lemma toRat_zero : (Dyadic.toRat (0 : Dyadic)) = 0 := by
  change ((0 : Int) : ℚ) * (2 : ℚ) ^ (0 : Int) = 0
  simp

@[simp] lemma toRat_one : (Dyadic.toRat (1 : Dyadic)) = 1 := by
  change ((1 : Int) : ℚ) * (2 : ℚ) ^ (0 : Int) = 1
  simp

@[simp] lemma toRat_neg (a : Dyadic) : Dyadic.toRat (-a) = - Dyadic.toRat a := by
  -- help `simp` by unfolding the projections of `-a`
  simp [Dyadic.toRat, (show (-a).man = -a.man by rfl), (show (-a).exp = a.exp by rfl)]

@[simp] lemma toRat_mul (a b : Dyadic) : Dyadic.toRat (a * b) = Dyadic.toRat a * Dyadic.toRat b := by
  -- `2 ≠ 0`, so we can use `zpow_add₀` in `ℚ`.
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  -- help `simp` by unfolding the projections of `a*b`
  simp [Dyadic.toRat, (show (a*b).man = a.man * b.man by rfl), (show (a*b).exp = a.exp + b.exp by rfl),
    zpow_add₀ h2, mul_assoc, mul_left_comm]

@[simp] lemma toRat_shiftl (x : Dyadic) (k : Int) :
    Dyadic.toRat (Dyadic.shiftl x k) = Dyadic.toRat x * ((2 : ℚ) ^ k) := by
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  -- help `simp` by unfolding the projections of `shiftl`
  simp [Dyadic.toRat, Dyadic.shiftl,
    zpow_add₀ h2, mul_left_comm, mul_comm]

@[simp] lemma toRat_add (a b : Dyadic) : Dyadic.toRat (a + b) = Dyadic.toRat a + Dyadic.toRat b := by
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  -- `Dyadic.add` aligns exponents; we split on the branch condition.
  by_cases h : a.exp ≤ b.exp
  · -- branch: result exponent is `a.exp`
    -- Expand `toRat` on the aligned representation.
    have hs_nonneg : 0 ≤ (b.exp - a.exp) := sub_nonneg.mpr h
    set s : Nat := (b.exp - a.exp).toNat
    have hs_cast : (s : Int) = (b.exp - a.exp) := by
      simpa [s] using (Int.toNat_of_nonneg hs_nonneg).symm
    have hshiftInt : (b.man <<< s : Int) = b.man * (2 : Int) ^ s := by
      simpa using (Int.shiftLeft_eq b.man s)
    have hbexp : b.exp = a.exp + (s : Int) := by
      -- `b = a + (b-a)` and rewrite `(b-a)` as `s`
      have : b.exp = a.exp + (b.exp - a.exp) := by abel
      simp [hs_cast]
    -- Convert the integer power in `hshiftInt` to a rational power.
    have hshiftRat : ((b.man <<< s : Int) : ℚ) = (b.man : ℚ) * (2 : ℚ) ^ (s : Nat) := by
      -- cast `b.man * (2:Int)^s` to ℚ
      have : ((b.man * (2 : Int) ^ s) : ℚ) = (b.man : ℚ) * (2 : ℚ) ^ (s : Nat) := by
        simp
      -- rewrite the LHS via `hshiftInt`
      simp [hshiftInt]
    have hzpowNat : (2 : ℚ) ^ (s : Int) = (2 : ℚ) ^ (s : Nat) := by
      -- `2^(↑s) = 2^s` (as a nat power), read backwards
      simp
    -- Main computation: unfold `a+b` and distribute.
    have hab : a + b = Dyadic.add a b := rfl
    -- rewrite the LHS projections using the chosen branch
    simp [hab, Dyadic.add, Dyadic.toRat, hshiftRat, hbexp, hzpowNat, zpow_add₀ h2,
      mul_add, mul_left_comm, mul_comm]
  · -- branch: result exponent is `b.exp`
    have h' : b.exp ≤ a.exp := le_of_not_ge h
    have hs_nonneg : 0 ≤ (a.exp - b.exp) := sub_nonneg.mpr h'
    set s : Nat := (a.exp - b.exp).toNat
    have hs_cast : (s : Int) = (a.exp - b.exp) := by
      simpa [s] using (Int.toNat_of_nonneg hs_nonneg).symm
    have hshiftInt : (a.man <<< s : Int) = a.man * (2 : Int) ^ s := by
      simpa using (Int.shiftLeft_eq a.man s)
    have haexp : a.exp = b.exp + (s : Int) := by
      have : a.exp = b.exp + (a.exp - b.exp) := by abel
      simp [hs_cast]
    have hshiftRat : ((a.man <<< s : Int) : ℚ) = (a.man : ℚ) * (2 : ℚ) ^ (s : Nat) := by
      have : ((a.man * (2 : Int) ^ s) : ℚ) = (a.man : ℚ) * (2 : ℚ) ^ (s : Nat) := by
        simp
      simp [hshiftInt]
    have hzpowNat : (2 : ℚ) ^ (s : Int) = (2 : ℚ) ^ (s : Nat) := by
      simp
    -- Avoid rewriting the `if`-condition with `haexp` (it causes a split on `s=0`).
    have hab : a + b = Dyadic.add a b := rfl
    -- First, unfold the chosen branch of `Dyadic.add` using `h` only.
    simp [hab, Dyadic.add, h, Dyadic.toRat, add_mul]
    -- Now rewrite the shifted term and exponent relation to match `a.toRat`.
    -- `((a.man <<< s):ℚ) * 2^b.exp = (a.man:ℚ) * 2^a.exp`.
    have h2z : (2 : ℚ) ≠ 0 := by norm_num
    -- `2^a.exp = 2^(b.exp + s) = 2^b.exp * 2^s`
    have hzpow : (2 : ℚ) ^ a.exp = (2 : ℚ) ^ b.exp * (2 : ℚ) ^ (s : Int) := by
      simpa [haexp] using (zpow_add₀ (a := (2 : ℚ)) h2z b.exp (s : Int))
    -- Turn `2^s` into a nat power so `hshiftRat` applies.
    have hzpow' : (2 : ℚ) ^ a.exp = (2 : ℚ) ^ b.exp * (2 : ℚ) ^ (s : Nat) := by
      simpa [hzpowNat] using hzpow
    -- Finish with commutativity/associativity.
    -- (At this point the goal is a ring identity over ℚ.)
    -- Use `hshiftRat` and reassociate.
    calc
      (↑(a.man <<< s) : ℚ) * (2 : ℚ) ^ b.exp
          = ((a.man : ℚ) * (2 : ℚ) ^ s) * (2 : ℚ) ^ b.exp := by
              simp [hshiftRat]
      _ = (a.man : ℚ) * ((2 : ℚ) ^ b.exp * (2 : ℚ) ^ s) := by
              ring_nf
      _ = (a.man : ℚ) * (2 : ℚ) ^ a.exp := by
              -- `hzpow' : 2^a.exp = 2^b.exp * 2^s`
              simp [hzpow']

@[simp] lemma toRat_sub (a b : Dyadic) : Dyadic.toRat (a - b) = Dyadic.toRat a - Dyadic.toRat b := by
  -- `a - b` is definitional `a + (-b)` for this dyadic implementation.
  calc
    Dyadic.toRat (a - b) = Dyadic.toRat (a + (-b)) := by rfl
    _ = Dyadic.toRat a + Dyadic.toRat (-b) := by simp
    _ = Dyadic.toRat a + (-Dyadic.toRat b) := by simp
    _ = Dyadic.toRat a - Dyadic.toRat b := by simp [sub_eq_add_neg]

/-!
### Certified rounding for the ApproxRationals interface
-/

/--
Certified error bound for the floor-based `approxRat` used by the fast dyadics.

This is the standard bracketing argument for `floor`:
if `m = floor(q * 2^n)`, then `m/2^n ≤ q < m/2^n + 1/2^n`.
-/
theorem abs_toRat_approxRat_sub_le (q : ℚ) (n : Nat) :
    |Dyadic.toRat (Dyadic.approxRat q n) - q| ≤ (1 : ℚ) / (2 ^ n) := by

  -- unfold the definitions; this reduces to a pure floor/ulp inequality in ℚ
  -- goal shape: `|m * (2^n)⁻¹ - q| ≤ (2^n)⁻¹` where `m = floor (q * 2^n)`
  simp [Dyadic.approxRat, Dyadic.toRat]
  -- abbreviations
  set p : ℚ := (2 : ℚ) ^ n
  have hp_pos : 0 < p := by
    dsimp [p]
    exact pow_pos (by norm_num : (0 : ℚ) < 2) n
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  set t : ℚ := q * p
  set m : Int := t.floor
  have hle : (m : ℚ) ≤ t := by
    simpa [m, t] using (Rat.floor_le t)
  have hlt : t < (m + 1 : ℚ) := by
    simpa [m, t] using (Rat.lt_floor_add_one t)
  -- lower bound: `m/p ≤ q`
  have hq_ge : (m : ℚ) * p⁻¹ ≤ q := by
    have hmul : (m : ℚ) * p⁻¹ ≤ t * p⁻¹ :=
      mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr (le_of_lt hp_pos))
    -- simplify `t * p⁻¹ = q`
    -- (`t = q*p` and `p ≠ 0`)
    simpa [t, p, mul_assoc, hp_ne] using hmul
  -- upper bound: `q < m/p + 1/p`
  have hq_lt : q < (m : ℚ) * p⁻¹ + p⁻¹ := by
    have hmul : t * p⁻¹ < (m + 1 : ℚ) * p⁻¹ :=
      mul_lt_mul_of_pos_right hlt (inv_pos.mpr hp_pos)
    -- simplify both sides
    -- `t * p⁻¹ = q`, and `(m+1)*p⁻¹ = m*p⁻¹ + p⁻¹`
    have ht : t * p⁻¹ = q := by
      -- `q * p * p⁻¹ = q`
      simp [t, p, hp_ne]
    have hm : (m + 1 : ℚ) * p⁻¹ = (m : ℚ) * p⁻¹ + p⁻¹ := by
      ring
    -- rewrite and conclude
    simpa [ht, hm] using hmul
  -- absolute value simplifies since `m/p ≤ q`
  have habs : |(m : ℚ) * p⁻¹ - q| = q - (m : ℚ) * p⁻¹ := by
    have hnonneg : 0 ≤ q - (m : ℚ) * p⁻¹ := sub_nonneg.mpr hq_ge
    -- `|a-b| = b-a` when `a ≤ b`
    simpa [abs_sub_comm] using (abs_of_nonneg hnonneg)
  have hdiff : q - (m : ℚ) * p⁻¹ ≤ p⁻¹ := by
    have : q - (m : ℚ) * p⁻¹ < p⁻¹ := by linarith [hq_lt]
    exact le_of_lt this
  -- finish
  calc
    |(m : ℚ) * p⁻¹ - q| = q - (m : ℚ) * p⁻¹ := habs
    _ ≤ p⁻¹ := hdiff
    _ ≤ (1 : ℚ) / (2 ^ n) := by
      -- this is just rewriting `p = (2:ℚ)^n` and `a⁻¹ = 1/a`
      simp [p, one_div]
  -- close the (definitional) inequality goal left by `calc`
  -- (Lean sometimes flips the last step when mixing `≤` and `=` reductions under `simp`.)
  simp [p, one_div]

/-- Error bound for `Int` floor division viewed in `ℚ`: the difference is at most `1`. -/
lemma abs_cast_ediv_sub_rat_div_le_one (num den : Int) (hden_pos : 0 < den) :
    |((num / den : Int) : ℚ) - (num : ℚ) / (den : ℚ)| ≤ (1 : ℚ) := by
  set q : Int := num / den
  set r : Int := num % den
  have hden_ne : den ≠ 0 := ne_of_gt hden_pos
  have hdecomp : den * q + r = num := by
    simpa [q, r, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, add_comm, add_left_comm, add_assoc] using
      (Int.mul_ediv_add_emod num den)
  have hr_nonneg : 0 ≤ r := Int.emod_nonneg num hden_ne
  have hr_lt : r < den := Int.emod_lt_of_pos num hden_pos
  have hdenQ_pos : (0 : ℚ) < (den : ℚ) := by exact_mod_cast hden_pos
  have hdenQ_ne : (den : ℚ) ≠ 0 := by exact_mod_cast hden_ne
  have hdiv : (num : ℚ) / (den : ℚ) = (q : ℚ) + (r : ℚ) / (den : ℚ) := by
    have hdecompQ : (den : ℚ) * (q : ℚ) + (r : ℚ) = (num : ℚ) := by
      exact_mod_cast hdecomp
    calc
      (num : ℚ) / (den : ℚ) = ((den : ℚ) * (q : ℚ) + (r : ℚ)) / (den : ℚ) := by
        simp [hdecompQ]
      _ = ((den : ℚ) * (q : ℚ)) / (den : ℚ) + (r : ℚ) / (den : ℚ) := by
        simp [add_div]
      _ = (q : ℚ) + (r : ℚ) / (den : ℚ) := by
        simp [mul_div_cancel_left₀, hdenQ_ne]
  have habs : |((q : Int) : ℚ) - (num : ℚ) / (den : ℚ)| = (r : ℚ) / (den : ℚ) := by
    calc
      |((q : Int) : ℚ) - (num : ℚ) / (den : ℚ)|
          = |((q : Int) : ℚ) - ((q : ℚ) + (r : ℚ) / (den : ℚ))| := by simp [hdiv]
      _ = |-( (r : ℚ) / (den : ℚ) )| := by ring_nf
      _ = (r : ℚ) / (den : ℚ) := by
        have hrQ_nonneg : (0 : ℚ) ≤ (r : ℚ) := by exact_mod_cast hr_nonneg
        have hdiv_nonneg : (0 : ℚ) ≤ (r : ℚ) / (den : ℚ) :=
          div_nonneg hrQ_nonneg (le_of_lt hdenQ_pos)
        simpa [abs_neg] using (abs_of_nonneg hdiv_nonneg)
  have hscaled_le_one : (r : ℚ) / (den : ℚ) ≤ (1 : ℚ) := by
    have hrQ_lt : (r : ℚ) < (den : ℚ) := by exact_mod_cast hr_lt
    have hrQ_le : (r : ℚ) ≤ (den : ℚ) := le_of_lt hrQ_lt
    exact (div_le_one hdenQ_pos).2 hrQ_le
  simpa [q, habs] using hscaled_le_one

/--
Certified error bound for `roundDown` at exponent `-n`.

This is the usual “floor bracketing” argument, specialized to powers of two and using
`Int` Euclidean division (which rounds toward `-∞`).
-/
theorem abs_toRat_roundDown_sub_le (d : Dyadic) (n : Nat) :
    |Dyadic.toRat (Dyadic.roundDown d (-(n : Int))) - Dyadic.toRat d| ≤ (1 : ℚ) / (2 ^ n) := by
  set min_exp : Int := (-(n : Int))
  by_cases h : d.exp >= min_exp
  · simp [Dyadic.roundDown, h, Dyadic.toRat, min_exp]
  · have hlt : d.exp < min_exp := lt_of_not_ge h
    have hshift_nonneg : 0 ≤ min_exp - d.exp := sub_nonneg.mpr (le_of_lt hlt)
    set sh : Nat := (min_exp - d.exp).toNat
    have hsh_cast : (sh : Int) = min_exp - d.exp := by
      simpa [sh] using (Int.toNat_of_nonneg hshift_nonneg).symm
    let den : Int := ((2 ^ sh : Nat) : Int)
    have hden_pos : (0 : Int) < den := by
      dsimp [den]
      have hnat : (0 : Nat) < 2 ^ sh := by
        simp
      exact_mod_cast hnat
    have h2ne : (2 : ℚ) ≠ 0 := by norm_num

    have hshift : d.man >>> sh = d.man / den := by
      simpa [den] using (Int.shiftRight_eq_div_pow d.man sh)

    have hround : Dyadic.toRat (Dyadic.roundDown d min_exp) =
        ((d.man / den : Int) : ℚ) * (2 : ℚ) ^ min_exp := by
      simp [Dyadic.roundDown, h, Dyadic.toRat, min_exp, sh, hshift, den]

    have hden_pow : (2 : ℚ) ^ (min_exp - d.exp) = (den : ℚ) := by
      have hx : min_exp - d.exp = (sh : Int) := by simpa using hsh_cast.symm
      calc
        (2 : ℚ) ^ (min_exp - d.exp) = (2 : ℚ) ^ (sh : Int) := by simp [hx]
        _ = (2 : ℚ) ^ sh := by simp
        _ = (den : ℚ) := by simp [den]

    have htoRat : Dyadic.toRat d = ((d.man : ℚ) / (den : ℚ)) * (2 : ℚ) ^ min_exp := by
      have hpow : (2 : ℚ) ^ d.exp = (2 : ℚ) ^ min_exp / (den : ℚ) := by
        have hdexp : d.exp = min_exp - (min_exp - d.exp) := by abel
        calc
          (2 : ℚ) ^ d.exp = (2 : ℚ) ^ (min_exp - (min_exp - d.exp)) := by
                simp
          _ = (2 : ℚ) ^ min_exp / (2 : ℚ) ^ (min_exp - d.exp) := by
                simpa using (zpow_sub₀ (a := (2 : ℚ)) h2ne min_exp (min_exp - d.exp))
          _ = (2 : ℚ) ^ min_exp / (den : ℚ) := by simp [hden_pow]
      calc
        Dyadic.toRat d = (d.man : ℚ) * (2 : ℚ) ^ d.exp := rfl
        _ = (d.man : ℚ) * ((2 : ℚ) ^ min_exp / (den : ℚ)) := by simp [hpow]
        _ = (d.man : ℚ) * (2 : ℚ) ^ min_exp / (den : ℚ) := by
              simp [mul_div_assoc']
        _ = ((d.man : ℚ) / (den : ℚ)) * (2 : ℚ) ^ min_exp := by
              symm
              simp [div_mul_eq_mul_div]

    have hfloor : |((d.man / den : Int) : ℚ) - (d.man : ℚ) / (den : ℚ)| ≤ (1 : ℚ) :=
      abs_cast_ediv_sub_rat_div_le_one d.man den hden_pos

    have hmin_pos : (0 : ℚ) < (2 : ℚ) ^ min_exp := zpow_pos (by norm_num : (0 : ℚ) < 2) _

    have hscaled :
        |((d.man / den : Int) : ℚ) * (2 : ℚ) ^ min_exp - ((d.man : ℚ) / (den : ℚ)) * (2 : ℚ) ^ min_exp|
          ≤ (2 : ℚ) ^ min_exp := by
      calc
        |((d.man / den : Int) : ℚ) * (2 : ℚ) ^ min_exp - ((d.man : ℚ) / (den : ℚ)) * (2 : ℚ) ^ min_exp|
            = |(((d.man / den : Int) : ℚ) - (d.man : ℚ) / (den : ℚ)) * (2 : ℚ) ^ min_exp| := by
                ring_nf
        _ = |((d.man / den : Int) : ℚ) - (d.man : ℚ) / (den : ℚ)| * |(2 : ℚ) ^ min_exp| := by
              simp [abs_mul]
        _ = |((d.man / den : Int) : ℚ) - (d.man : ℚ) / (den : ℚ)| * (2 : ℚ) ^ min_exp := by
              simp [abs_of_pos hmin_pos]
        _ ≤ (1 : ℚ) * (2 : ℚ) ^ min_exp := by
              gcongr
        _ = (2 : ℚ) ^ min_exp := by ring

    calc
      |Dyadic.toRat (Dyadic.roundDown d min_exp) - Dyadic.toRat d|
          = |((d.man / den : Int) : ℚ) * (2 : ℚ) ^ min_exp - ((d.man : ℚ) / (den : ℚ)) * (2 : ℚ) ^ min_exp| := by
                simp [hround, htoRat]
      _ ≤ (2 : ℚ) ^ min_exp := hscaled
      _ = (1 : ℚ) / (2 ^ n) := by
            simp [min_exp, one_div]

/--
Certified error bound for `divDown` at exponent `-n`.

The core of the proof is again floor bracketing for integer Euclidean division:
for `den > 0`, if `q = num / den`, then `|q - num/den| ≤ 1`.
-/
theorem abs_toRat_divDown_sub_le (a b : Dyadic) (n : Nat) :
    |Dyadic.toRat (Dyadic.divDown a b (-(n : Int))) - (Dyadic.toRat a / Dyadic.toRat b)|
      ≤ (1 : ℚ) / (2 ^ n) := by
  set prec : Int := (-(n : Int))
  by_cases hb : b.man == 0
  · have hb0 : b.man = 0 := by simpa using hb
    have hbRat : Dyadic.toRat b = 0 := by simp [Dyadic.toRat, hb0]
    -- `divDown` returns `0` and `a / 0 = 0` in `ℚ`
    simp [Dyadic.divDown, hb0, hbRat]
  · have hb0 : b.man ≠ 0 := by
      intro h
      apply hb
      simp [h]

    set num0den0 : Int × Int := Dyadic.scaledNumDen a b prec
    set num0 : Int := num0den0.1
    set den0 : Int := num0den0.2
    set numden : Int × Int := Dyadic.normalizeDivisor num0 den0
    set num : Int := numden.1
    set den : Int := numden.2
    set shift : Int := a.exp - b.exp - prec

    have hden0_ne : den0 ≠ 0 := by
      by_cases hs : shift >= 0
      · have hcond : prec ≤ a.exp - b.exp := (sub_nonneg).1 (by simpa [shift] using hs)
        have hden0 : den0 = b.man := by
          simp [den0, num0den0, Dyadic.scaledNumDen, hcond]
        simpa [hden0] using hb0
      · have hs' : shift < 0 := lt_of_not_ge hs
        have hcond : ¬ prec ≤ a.exp - b.exp := by
          intro hle
          have : 0 ≤ a.exp - b.exp - prec := (sub_nonneg).2 hle
          exact hs (by simpa [shift] using this)
        have hden0 : den0 = b.man <<< (prec - (a.exp - b.exp)).toNat := by
          simp [den0, num0den0, Dyadic.scaledNumDen, hcond]
        have hkpos : 0 < (2 : Int) ^ (prec - (a.exp - b.exp)).toNat := by
          have h2pos : (0 : Int) < (2 : Int) := by decide
          exact Int.pow_pos (n := (2 : Int)) (m := (prec - (a.exp - b.exp)).toNat) h2pos
        have hshift_ne : (b.man <<< (prec - (a.exp - b.exp)).toNat) ≠ 0 := by
          have : b.man * (2 : Int) ^ (prec - (a.exp - b.exp)).toNat ≠ 0 :=
            mul_ne_zero hb0 (ne_of_gt hkpos)
          simpa [Int.shiftLeft_eq] using this
        simpa [hden0] using hshift_ne

    have hden_pos : (0 : Int) < den := by
      dsimp [den, numden, Dyadic.normalizeDivisor]
      by_cases hneg : den0 < 0
      · have : 0 < -den0 := by linarith
        simp [hneg]
      · have hnonneg : 0 ≤ den0 := le_of_not_gt hneg
        have hpos : 0 < den0 := lt_of_le_of_ne hnonneg (Ne.symm hden0_ne)
        simp [hneg, hpos]

    have hfloor : |((num / den : Int) : ℚ) - (num : ℚ) / (den : ℚ)| ≤ (1 : ℚ) :=
      abs_cast_ediv_sub_rat_div_le_one num den hden_pos

    have h2ne : (2 : ℚ) ≠ 0 := by norm_num
    have hprec_pos : (0 : ℚ) < (2 : ℚ) ^ prec := zpow_pos (by norm_num : (0 : ℚ) < 2) _

    have hdivDown_toRat :
        Dyadic.toRat (Dyadic.divDown a b prec) = ((num / den : Int) : ℚ) * (2 : ℚ) ^ prec := by
      simp [Dyadic.divDown, hb, Dyadic.toRat, prec, num0den0, num0, den0, numden, num, den]

    have hnumden_eq : (num : ℚ) / (den : ℚ) = (num0 : ℚ) / (den0 : ℚ) := by
      dsimp [num, den, numden, Dyadic.normalizeDivisor]
      by_cases hneg : den0 < 0
      · simp [hneg, div_eq_mul_inv]
      · simp [hneg]

    have hnum0den0_ratio : (num0 : ℚ) / (den0 : ℚ) = ((a.man : ℚ) / (b.man : ℚ)) * (2 : ℚ) ^ shift := by
      by_cases hs : shift >= 0
      · have hs' : 0 ≤ shift := hs
        have hcond : prec ≤ a.exp - b.exp := (sub_nonneg).1 (by simpa [shift] using hs)
        have hnum0 : num0 = a.man <<< shift.toNat := by
          simp [num0, num0den0, Dyadic.scaledNumDen, shift, hcond]
        have hden0 : den0 = b.man := by
          simp [den0, num0den0, Dyadic.scaledNumDen, hcond]
        have hk : (shift.toNat : Int) = shift := by
          simpa using (Int.toNat_of_nonneg hs').symm
        have hpow : (2 : ℚ) ^ shift.toNat = (2 : ℚ) ^ shift := by
          have : (2 : ℚ) ^ shift = (2 : ℚ) ^ shift.toNat := by
            calc
              (2 : ℚ) ^ shift = (2 : ℚ) ^ (shift.toNat : Int) := by simp [hk]
              _ = (2 : ℚ) ^ shift.toNat := by simpa using (zpow_natCast (2 : ℚ) shift.toNat)
          exact this.symm
        calc
          (num0 : ℚ) / (den0 : ℚ)
              = ((a.man <<< shift.toNat : Int) : ℚ) / (b.man : ℚ) := by simp [hnum0, hden0]
          _ = ((a.man : ℚ) / (b.man : ℚ)) * (2 : ℚ) ^ shift.toNat := by
                simpa [Int.shiftLeft_eq] using
                  (div_mul_eq_mul_div (a.man : ℚ) (b.man : ℚ) ((2 : ℚ) ^ shift.toNat)).symm
          _ = ((a.man : ℚ) / (b.man : ℚ)) * (2 : ℚ) ^ shift := by simp [hpow]
      · have hs' : shift < 0 := lt_of_not_ge hs
        have hcond : ¬ prec ≤ a.exp - b.exp := by
          intro hle
          have : 0 ≤ a.exp - b.exp - prec := (sub_nonneg).2 hle
          exact hs (by simpa [shift] using this)
        have hnum0 : num0 = a.man := by
          simp [num0, num0den0, Dyadic.scaledNumDen, hcond]
        have hden0 : den0 = b.man <<< (prec - (a.exp - b.exp)).toNat := by
          simp [den0, num0den0, Dyadic.scaledNumDen, hcond]
        -- negative shift case: divide by shifted denominator
        let k : Nat := (-shift).toNat
        have hk : (k : Int) = -shift := by
          have : 0 ≤ -shift := by linarith
          simpa [k] using (Int.toNat_of_nonneg this).symm
        have hshift : shift = -(k : Int) := by
          simpa [k] using (congrArg Neg.neg hk).symm
        have hshiftLeft : ((b.man <<< k : Int) : ℚ) = (b.man : ℚ) * (2 : ℚ) ^ k := by
          simp [Int.shiftLeft_eq]
        have hinv : ((2 : ℚ) ^ k)⁻¹ = (2 : ℚ) ^ (-(k : Int)) := by
          simp [zpow_natCast]
        have hneg_case :
            ((a.man : ℚ) / ((b.man <<< k : Int) : ℚ)) = ((a.man : ℚ) / (b.man : ℚ)) * (2 : ℚ) ^ shift := by
          calc
            (a.man : ℚ) / ((b.man <<< k : Int) : ℚ)
                = (a.man : ℚ) / ((b.man : ℚ) * (2 : ℚ) ^ k) := by
                      simp [hshiftLeft]
            _ = (a.man : ℚ) / (b.man : ℚ) / (2 : ℚ) ^ k := by
                  simp [div_mul_eq_div_div]
            _ = (a.man : ℚ) / (b.man : ℚ) * ((2 : ℚ) ^ k)⁻¹ := by
                  simp [div_eq_mul_inv]
            _ = (a.man : ℚ) / (b.man : ℚ) * (2 : ℚ) ^ (-(k : Int)) := by
                  simp
            _ = (a.man : ℚ) / (b.man : ℚ) * (2 : ℚ) ^ shift := by
                  simp [hshift]
        -- substitute back `k = (-shift).toNat`
        have hk_def : k = (-shift).toNat := rfl
        -- and finish
        have hksimp : (b.man <<< (prec - (a.exp - b.exp)).toNat : Int) = (b.man <<< k : Int) := by
          -- `prec - (a.exp - b.exp) = -shift`
          have : prec - (a.exp - b.exp) = -shift := by
            dsimp [shift]
            abel
          simp [k, this]
        -- rewrite the denominator and apply `hneg_case`
        simpa [hnum0, hden0, hksimp] using hneg_case

    have hshift_add : shift + prec = a.exp - b.exp := by
      -- `shift = a.exp - b.exp - prec`
      dsimp [shift]
      abel
    have hzpow : (2 : ℚ) ^ (a.exp - b.exp) = (2 : ℚ) ^ shift * (2 : ℚ) ^ prec := by
      calc
        (2 : ℚ) ^ (a.exp - b.exp) = (2 : ℚ) ^ (shift + prec) := by simp [hshift_add]
        _ = (2 : ℚ) ^ shift * (2 : ℚ) ^ prec := by
              simpa using (zpow_add₀ (a := (2 : ℚ)) h2ne shift prec)

    have hratio_scaled : Dyadic.toRat a / Dyadic.toRat b = ((num : ℚ) / (den : ℚ)) * (2 : ℚ) ^ prec := by
      -- compute `toRat a / toRat b` as mantissa ratio and exponent difference
      have htoRat_div : Dyadic.toRat a / Dyadic.toRat b =
          ((a.man : ℚ) / (b.man : ℚ)) * (2 : ℚ) ^ (a.exp - b.exp) := by
        simp [Dyadic.toRat, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, zpow_sub₀ h2ne]
      -- combine the exponent split and `scaledNumDen`
      calc
        Dyadic.toRat a / Dyadic.toRat b
            = ((a.man : ℚ) / (b.man : ℚ)) * (2 : ℚ) ^ (a.exp - b.exp) := htoRat_div
        _ = ((a.man : ℚ) / (b.man : ℚ)) * ((2 : ℚ) ^ shift * (2 : ℚ) ^ prec) := by
              simp [hzpow]
        _ = (((a.man : ℚ) / (b.man : ℚ)) * (2 : ℚ) ^ shift) * (2 : ℚ) ^ prec := by ring_nf
        _ = ((num0 : ℚ) / (den0 : ℚ)) * (2 : ℚ) ^ prec := by
              simp [hnum0den0_ratio]
        _ = ((num : ℚ) / (den : ℚ)) * (2 : ℚ) ^ prec := by
              simp [hnumden_eq]

    have herr :
        |((num / den : Int) : ℚ) * (2 : ℚ) ^ prec - ((num : ℚ) / (den : ℚ)) * (2 : ℚ) ^ prec|
          ≤ (2 : ℚ) ^ prec := by
      calc
        |((num / den : Int) : ℚ) * (2 : ℚ) ^ prec - ((num : ℚ) / (den : ℚ)) * (2 : ℚ) ^ prec|
            = |(((num / den : Int) : ℚ) - (num : ℚ) / (den : ℚ)) * (2 : ℚ) ^ prec| := by ring_nf
        _ = |((num / den : Int) : ℚ) - (num : ℚ) / (den : ℚ)| * |(2 : ℚ) ^ prec| := by
              simp [abs_mul]
        _ = |((num / den : Int) : ℚ) - (num : ℚ) / (den : ℚ)| * (2 : ℚ) ^ prec := by
              simp [abs_of_pos hprec_pos]
        _ ≤ (1 : ℚ) * (2 : ℚ) ^ prec := by
              gcongr
        _ = (2 : ℚ) ^ prec := by ring

    calc
      |Dyadic.toRat (Dyadic.divDown a b prec) - (Dyadic.toRat a / Dyadic.toRat b)|
          = |((num / den : Int) : ℚ) * (2 : ℚ) ^ prec - ((num : ℚ) / (den : ℚ)) * (2 : ℚ) ^ prec| := by
                simp [hdivDown_toRat, hratio_scaled]
      _ ≤ (2 : ℚ) ^ prec := herr
      _ = (1 : ℚ) / (2 ^ n) := by
            simp [prec, one_div]

end Dyadic
end Computable.Fast

namespace Computable

open Computable.Fast

/-!
### ApproxRationals instance for the fast dyadics

This lets us reuse the existing `CRealRep`/`CRealAQ` infrastructure with the new backend.
-/

instance : ApproxRationals Computable.Fast.Dyadic where
  toRat := Computable.Fast.Dyadic.toRat
  toRat_zero := by simp
  toRat_one := by simp
  toRat_add := by intro a b; simp
  toRat_neg := by intro a; simp
  toRat_sub := by intro a b; simp
  toRat_mul := by intro a b; simp
  shiftl := fun x k => Computable.Fast.Dyadic.shiftl x k
  toRat_shiftl := by intro x k; simp
  -- Fast certified rounding: bitshift-based `roundDown`.
  approx := fun x n => Computable.Fast.Dyadic.roundDown x (-(n : Int))
  abs_toRat_approx_sub_le := by
    intro x n
    simpa using (Computable.Fast.Dyadic.abs_toRat_roundDown_sub_le (d := x) (n := n))
  approxRat := fun q n => Computable.Fast.Dyadic.approxRat q n
  abs_toRat_approxRat_sub_le := by
    intro q n
    simpa using (Computable.Fast.Dyadic.abs_toRat_approxRat_sub_le (q := q) (n := n))
  -- Fast certified division: bitshift+`Int` floor division at target exponent `-n`.
  appDiv := fun x y n => Computable.Fast.Dyadic.divDown x y (-(n : Int))
  abs_toRat_appDiv_sub_le := by
    intro x y n
    simpa using (Computable.Fast.Dyadic.abs_toRat_divDown_sub_le (a := x) (b := y) (n := n))

/-- Fast representatives backed by `Computable.Fast.Dyadic`. -/
abbrev CRealFastRep : Type := CRealRep Computable.Fast.Dyadic

/-- Fast extensional quotient backed by `Computable.Fast.Dyadic`. -/
abbrev CRealFast : Type := CRealAQ Computable.Fast.Dyadic

namespace CRealFast

/-- Denotation into the proof-level quotient `CReal`. -/
abbrev toCReal : CRealFast → CReal := CRealAQ.toCReal (AQ := Computable.Fast.Dyadic)

/-- Canonical embedding from the proof-level quotient `CReal`. -/
abbrev ofCReal : CReal → CRealFast := CRealAQ.ofCReal (AQ := Computable.Fast.Dyadic)

/-- Equivalence between the fast dyadic quotient and the proof quotient. -/
abbrev equivCReal : CRealFast ≃ CReal := CRealAQ.equivCReal (AQ := Computable.Fast.Dyadic)

/-- Ring equivalence between the fast dyadic quotient and the proof quotient. -/
abbrev ringEquivCReal : CRealFast ≃+* CReal := CRealAQ.ringEquivCReal (AQ := Computable.Fast.Dyadic)

end CRealFast

end Computable
