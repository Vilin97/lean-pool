/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Star

namespace Computable.Fast

/-!
## 1. The Engine: Raw Dyadic Arithmetic
A raw Dyadic number: `man * 2^exp`.
Uses `Int` (GMP) for high-performance arbitrary precision arithmetic.
-/
structure Dyadic where
  man : Int
  exp : Int
deriving Inhabited, Repr, DecidableEq

namespace Dyadic

/-- Convert to Rational for specification (not execution). -/
def toRat (d : Dyadic) : ℚ :=
  (d.man : ℚ) * (2 : ℚ) ^ d.exp

/-- `2^e` as a `Float` for `e : Int` (handles negative exponents). -/
@[inline] def pow2Float (e : Int) : Float :=
  Float.pow 2.0 (Float.ofInt e)

/-- Convert to Float for human-readable `#eval` output. -/
def toFloat (d : Dyadic) : Float :=
  (Float.ofInt d.man) * pow2Float d.exp

instance : ToString Dyadic where
  toString d := toString (d.toFloat)

/--
**Fast Rounding**:
Reduces precision using bit-shifts. Rounds to nearest (ties to even/up).
Target: Result will have exponent `min_exp`.
-/
@[inline] private def pow2Int (k : Nat) : Int :=
  (1 : Int) <<< k

/-- Round down (toward `-∞`) to the target exponent `min_exp`. -/
@[inline] def roundDown (d : Dyadic) (min_exp : Int) : Dyadic :=
  if d.exp >= min_exp then d
  else
    let shift := (min_exp - d.exp).toNat
    { man := d.man >>> shift, exp := min_exp }

/-- Round up (toward `+∞`) to the target exponent `min_exp`. -/
@[inline] def roundUp (d : Dyadic) (min_exp : Int) : Dyadic :=
  if d.exp >= min_exp then d
  else
    let shift := (min_exp - d.exp).toNat
    let denom : Int := pow2Int shift
    let q := d.man >>> shift
    let r := d.man % denom
    { man := if r == 0 then q else q + 1, exp := min_exp }

/-- Round to nearest; ties go to even (banker's rounding). -/
@[inline] def round (d : Dyadic) (min_exp : Int) : Dyadic :=
  if d.exp >= min_exp then d
  else
    let shift := (min_exp - d.exp).toNat
    let denom : Int := pow2Int shift
    let q := d.man >>> shift
    let r := d.man % denom
    let half : Int := denom >>> 1
    let q' :=
      if r < half then q
      else if r > half then q + 1
      else if q % 2 == 0 then q else q + 1
    { man := q', exp := min_exp }

def neg (a : Dyadic) : Dyadic :=
  { man := -a.man, exp := a.exp }

def add (a b : Dyadic) : Dyadic :=
  -- Align exponents
  if a.exp <= b.exp then
    let shift := (b.exp - a.exp).toNat
    { man := a.man + (b.man <<< shift), exp := a.exp }
  else
    let shift := (a.exp - b.exp).toNat
    { man := (a.man <<< shift) + b.man, exp := b.exp }

def mul (a b : Dyadic) : Dyadic :=
  { man := a.man * b.man, exp := a.exp + b.exp }

def abs (a : Dyadic) : Dyadic :=
  { man := a.man.natAbs, exp := a.exp }

instance : Zero Dyadic := ⟨⟨0, 0⟩⟩
instance : One Dyadic := ⟨⟨1, 0⟩⟩

instance : Add Dyadic := ⟨add⟩
instance : Mul Dyadic := ⟨mul⟩
instance : Neg Dyadic := ⟨neg⟩

def lt (a b : Dyadic) : Prop :=
  if a.exp <= b.exp then
    let shift := (b.exp - a.exp).toNat
    a.man < (b.man <<< shift)
  else
    let shift := (a.exp - b.exp).toNat
    (a.man <<< shift) < b.man

instance : LT Dyadic := ⟨lt⟩
instance (a b : Dyadic) : Decidable (a < b) := by
  change Decidable (Dyadic.lt a b)
  unfold Dyadic.lt
  by_cases h : a.exp <= b.exp
  · simp [h]; exact a.man.decLt (b.man <<< (b.exp - a.exp).toNat)
  · simp [h]; exact (a.man <<< (a.exp - b.exp).toNat).decLt b.man

def le (a b : Dyadic) : Prop := a < b ∨ a = b
instance : LE Dyadic := ⟨le⟩
instance (a b : Dyadic) : Decidable (a ≤ b) :=
  if h : a < b then isTrue (Or.inl h)
  else if h' : a = b then isTrue (Or.inr h')
  else isFalse (fun | Or.inl l => h l | Or.inr e => h' e)

@[inline] private def divPow2Ceil (n : Int) (k : Nat) : Int :=
  let denom : Int := pow2Int k
  let q := n >>> k
  let r := n % denom
  if r == 0 then q else q + 1

/-- Square root, rounded down (toward `-∞`) at target exponent `prec`. -/
def sqrt (d : Dyadic) (prec : Int) : Dyadic :=
  if d.man < 0 then { man := 0, exp := prec }
  else
    let shift_amount := d.exp - 2 * prec
    let val : Int :=
      if shift_amount >= 0 then d.man <<< shift_amount.toNat
      else d.man >>> (-shift_amount).toNat
    let valNat : Nat := val.toNat
    let s : Nat := Nat.sqrt valNat
    { man := s, exp := prec }

/-- Square root, rounded up (toward `+∞`) at target exponent `prec`. -/
def sqrtUp (d : Dyadic) (prec : Int) : Dyadic :=
  if d.man < 0 then { man := 0, exp := prec }
  else
    let shift_amount := d.exp - 2 * prec
    let val : Int :=
      if shift_amount >= 0 then d.man <<< shift_amount.toNat
      else divPow2Ceil d.man (-shift_amount).toNat
    let valNat : Nat := val.toNat
    let s : Nat := Nat.sqrt valNat
    let s' : Nat := if s * s == valNat then s else s + 1
    { man := s', exp := prec }

@[inline] def normalizeDivisor (num den : Int) : Int × Int :=
  if den < 0 then (-num, -den) else (num, den)

@[inline] def scaledNumDen (a b : Dyadic) (prec : Int) : Int × Int :=
  let shift := a.exp - b.exp - prec
  if shift >= 0 then
    (a.man <<< shift.toNat, b.man)
  else
    (a.man, b.man <<< (-shift).toNat)

/--
Divide dyadics at target exponent `prec`, rounding down (toward `-∞`).

If `b.man = 0`, this returns `0` (callers that care about correctness should
guard against division by zero at the `Ball`/`FastReal` layer).
-/
def divDown (a b : Dyadic) (prec : Int) : Dyadic :=
  if b.man == 0 then 0
  else
    let (num0, den0) := scaledNumDen a b prec
    let (num, den) := normalizeDivisor num0 den0
    { man := num / den, exp := prec }

/--
Divide dyadics at target exponent `prec`, rounding up (toward `+∞`).

If `b.man = 0`, this returns `0` (callers that care about correctness should
guard against division by zero at the `Ball`/`FastReal` layer).
-/
def divUp (a b : Dyadic) (prec : Int) : Dyadic :=
  if b.man == 0 then 0
  else
    let (num0, den0) := scaledNumDen a b prec
    let (num, den) := normalizeDivisor num0 den0
    let q := num / den
    let r := num % den
    { man := if r == 0 then q else q + 1, exp := prec }

/--
Divide dyadics at target exponent `prec`, rounding to nearest (ties to even).

If `b.man = 0`, this returns `0` (callers that care about correctness should
guard against division by zero at the `Ball`/`FastReal` layer).
-/
def div (a b : Dyadic) (prec : Int) : Dyadic :=
  if b.man == 0 then 0
  else
    let (num0, den0) := scaledNumDen a b prec
    let (num, den) := normalizeDivisor num0 den0
    let q := num / den
    let r := num % den
    let two_r := 2 * r
    let q' :=
      if two_r < den then q
      else if two_r > den then q + 1
      else if q % 2 == 0 then q else q + 1
    { man := q', exp := prec }

def sub (a b : Dyadic) : Dyadic := add a (neg b)
instance : Sub Dyadic := ⟨sub⟩

def floor (d : Dyadic) : Int :=
  if d.exp >= 0 then d.man * ((1 : Int) <<< d.exp.toNat)
  else d.man >>> (-d.exp).toNat

def ceil (d : Dyadic) : Int :=
  if d.exp >= 0 then d.man * ((1 : Int) <<< d.exp.toNat)
  else
    let shift := (-d.exp).toNat
    let mask := ((1 : Int) <<< shift) - 1
    (d.man + mask) >>> shift

def sign (d : Dyadic) : Int :=
  if d.man > 0 then 1 else if d.man < 0 then -1 else 0

def shiftl (d : Dyadic) (k : Int) : Dyadic :=
  { man := d.man, exp := d.exp + k }

def approxRat (q : ℚ) (n : Nat) : Dyadic :=
  let e := -(n : Int)
  let m := (q * (2 : ℚ)^n).floor
  { man := m, exp := e }

end Dyadic

/-! # 2. The Container: Interval (Ball) Arithmetic -/

/-- A Ball [mid ± rad]. -/
structure Ball where
  mid : Dyadic
  rad : Dyadic
deriving Repr, DecidableEq, Inhabited

namespace Ball

def zero : Ball := ⟨⟨0,0⟩, ⟨0,0⟩⟩
def one  : Ball := ⟨⟨1,0⟩, ⟨0,0⟩⟩

/--
**Precision Manager**:
Operations take a `prec` argument (target exponent, e.g., -64).
We round the result to this precision to stop expression swell.
-/
def add (x y : Ball) (prec : Int) : Ball :=
  let raw_mid := x.mid + y.mid
  let new_mid := raw_mid.round prec
  -- Rounding error bound: 2^(prec-1)
  let err : Dyadic := ⟨1, prec - 1⟩
  -- Radius: r1 + r2 + error
  let raw_rad := x.rad + y.rad + err
  { mid := new_mid, rad := raw_rad.abs.roundUp prec }

def neg (x : Ball) : Ball :=
  { mid := -x.mid, rad := x.rad }

def mul (x y : Ball) (prec : Int) : Ball :=
  let raw_mid := x.mid * y.mid
  let new_mid := raw_mid.round prec
  let err : Dyadic := ⟨1, prec - 1⟩
  -- Product rule error: |x|ry + |y|rx + rx*ry
  let term1 := x.mid.abs * y.rad
  let term2 := y.mid.abs * x.rad
  let term3 := x.rad * y.rad
  let raw_rad := term1 + term2 + term3 + err
  { mid := new_mid, rad := raw_rad.abs.roundUp prec }

def ofDyadic (d : Dyadic) : Ball := ⟨d, ⟨0, 0⟩⟩

@[inline] def lo (b : Ball) : Dyadic := b.mid - b.rad
@[inline] def hi (b : Ball) : Dyadic := b.mid + b.rad

/--
Build a `Ball` enclosing the dyadic interval `[lo, hi]`, rounded to exponent `prec`.

This is the main “interval-to-ball” adapter; it takes care of midpoint rounding error.
-/
def ofInterval (lo hi : Dyadic) (prec : Int) : Ball :=
  let half : Dyadic := ⟨1, -1⟩
  let raw_mid := (lo + hi) * half
  let new_mid := raw_mid.round prec
  let err : Dyadic := ⟨1, prec - 1⟩
  let raw_rad := (hi - lo).abs * half + err
  { mid := new_mid, rad := raw_rad.roundUp prec }

/-- Upper bound on `|x|` for any `x` in this ball. -/
def absUpper (b : Ball) : Dyadic :=
  let lo := b.lo
  let hi := b.hi
  let alo := lo.abs
  let ahi := hi.abs
  if alo < ahi then ahi else alo

/-- Scale by a power of two: `scale2 b k` represents `b * 2^k`. -/
@[inline] def scale2 (b : Ball) (k : Int) : Ball :=
  { mid := b.mid.shiftl k, rad := b.rad.shiftl k }

def sqrt (x : Ball) (prec : Int) : Ball :=
  let lo := x.lo
  let hi := x.hi
  if hi.man < 0 then zero
  else
    let lo' : Dyadic := if lo.man < 0 then 0 else lo
    ofInterval (lo'.sqrt prec) (hi.sqrtUp prec) prec

def abs (x : Ball) (prec : Int) : Ball :=
  let lo := x.lo
  let hi := x.hi
  if lo.man >= 0 then
    ofInterval lo hi prec
  else if hi.man <= 0 then
    ofInterval (-hi) (-lo) prec
  else
    let neg_lo : Dyadic := -lo
    let m : Dyadic := if neg_lo < hi then hi else neg_lo
    ofInterval 0 m prec

def pow (x : Ball) (n : Nat) (prec : Int) : Ball :=
  Nat.rec (motive := fun _ => Ball) one (fun _ acc => mul acc x prec) n

def floor (b : Ball) : Option Int :=
  let min := b.mid - b.rad
  let max := b.mid + b.rad
  let f_min := min.floor
  let f_max := max.floor
  if f_min == f_max then some f_min else none

def ceil (b : Ball) : Option Int :=
  let min := b.mid - b.rad
  let max := b.mid + b.rad
  let c_min := min.ceil
  let c_max := max.ceil
  if c_min == c_max then some c_min else none

def min (x y : Ball) (prec : Int) : Ball :=
  let x_lo := x.lo
  let x_hi := x.hi
  let y_lo := y.lo
  let y_hi := y.hi
  let m_lo := if x_lo < y_lo then x_lo else y_lo
  let m_hi := if x_hi < y_hi then x_hi else y_hi
  ofInterval m_lo m_hi prec

def max (x y : Ball) (prec : Int) : Ball :=
  let x_lo := x.lo
  let x_hi := x.hi
  let y_lo := y.lo
  let y_hi := y.hi
  let m_lo := if x_lo < y_lo then y_lo else x_lo
  let m_hi := if x_hi < y_hi then y_hi else x_hi
  ofInterval m_lo m_hi prec

/--
Reciprocal of a ball at precision `prec`, if the interval is separated from `0`.

Returns `none` if the interval straddles `0`, because the image of the interval under
`x ↦ 1/x` is unbounded.
-/
def inv? (x : Ball) (prec : Int) : Option Ball :=
  let lo := x.lo
  let hi := x.hi
  if hi.man < 0 then
    -- lo < hi < 0, so `1/hi ≤ 1/x ≤ 1/lo`
    let loInv := Dyadic.divDown 1 hi prec
    let hiInv := Dyadic.divUp 1 lo prec
    some (ofInterval loInv hiInv prec)
  else if lo.man > 0 then
    -- 0 < lo ≤ hi, so `1/hi ≤ 1/x ≤ 1/lo`
    let loInv := Dyadic.divDown 1 hi prec
    let hiInv := Dyadic.divUp 1 lo prec
    some (ofInterval loInv hiInv prec)
  else
    none

/-- Divide `x` by `y` at precision `prec`, if `y` is separated from `0`. -/
def div? (x y : Ball) (prec : Int) : Option Ball := do
  let invy ← inv? y prec
  pure (mul x invy prec)

/-- Reciprocal of a nonzero dyadic, as a `Ball`. -/
def invDyadic? (d : Dyadic) (prec : Int) : Option Ball :=
  if d.man == 0 then none
  else
    let lo := Dyadic.divDown 1 d prec
    let hi := Dyadic.divUp 1 d prec
    some (ofInterval lo hi prec)

@[inline] private def invDyadic (d : Dyadic) (prec : Int) : Ball :=
  (invDyadic? d prec).getD zero

@[inline] private def divDyadic (x : Ball) (d : Dyadic) (prec : Int) : Ball :=
  mul x (invDyadic d prec) prec

def exp (x : Ball) (prec : Int) : Ball :=
  -- Scale down so that `|x_small|` is tiny (≈ ≤ 1/4), making the Taylor tail easy to bound.
  let u := x.absUpper
  let mag := u.exp + (if u.man = 0 then 0 else u.man.natAbs.log2)
  let k : Int := if mag > -2 then mag + 2 else 0
  let k_nat := k.toNat
  let x_small := x.scale2 (-k)

  -- Stop once the next term is below this threshold.
  let tol : Dyadic := ⟨1, prec - 4⟩
  let maxTerms : Nat := (-prec).toNat + 64

  -- term₀ = 1, sum₀ = 1, term_{i+1} = term_i * x / (i+1)
  let rec taylor (fuel : Nat) (term sum : Ball) (i : Nat) : Ball :=
    match fuel with
    | 0 => sum
    | fuel + 1 =>
      let i1 := i + 1
      let term' := divDyadic (mul term x_small prec) ⟨(i1 : Int), 0⟩ prec
      let sum' := add sum term' prec
      if term'.absUpper < tol then
        -- With `|x_small| ≤ 1/4`, the remaining tail is bounded by a small geometric series.
        -- A simple safe bound is `2 * |term'|`.
        let tail := (term'.absUpper * ⟨2, 0⟩).roundUp prec
        { mid := sum'.mid, rad := (sum'.rad + tail).roundUp prec }
      else
        taylor fuel term' sum' i1

  let y_small := taylor maxTerms one one 0

  let rec square (y : Ball) : Nat → Ball
    | 0 => y
    | count + 1 => square (mul y y prec) count

  square y_small k_nat

def ln2 (prec : Int) : Ball :=
  let y := divDyadic one ⟨3, 0⟩ prec
  let y2 := mul y y prec
  let tol : Dyadic := ⟨1, prec - 4⟩
  let maxTerms : Nat := (-prec).toNat + 64

  -- ln(2) = 2 * Σ_{k>=0} (y^(2k+1) / (2k+1)), with y = 1/3 (geometric decay, ratio = 1/9).
  let rec loop (fuel : Nat) (t sum : Ball) (k : Nat) : Ball :=
    match fuel with
    | 0 => sum
    | fuel + 1 =>
      let term := divDyadic t ⟨(2 * k + 1 : Int), 0⟩ prec
      let sum' := add sum term prec
      let t' := mul t y2 prec
      let k' := k + 1
      let termNext := divDyadic t' ⟨(2 * k' + 1 : Int), 0⟩ prec
      if termNext.absUpper < tol then
        let tail := (termNext.absUpper * ⟨2, 0⟩).roundUp prec
        { mid := sum'.mid, rad := (sum'.rad + tail).roundUp prec }
      else
        loop fuel t' sum' k'

  let s := loop maxTerms y zero 0
  mul s (ofDyadic ⟨2, 0⟩) prec

/--
Natural logarithm on balls, as a **partial** operation.

We return `none` unless the ball is *provably positive* (its lower endpoint is `> 0`).
-/
def log? (x : Ball) (prec : Int) : Option Ball := do
  let lo := x.lo
  if lo.man <= 0 then none
  else
    let m := x.mid.man
    let e := x.mid.exp
    let shift := - ((m.natAbs.log2 : Int) + e)
    let x_norm := mul x (ofDyadic ⟨1, shift⟩) prec
    let num := add x_norm (neg one) prec
    let den := add x_norm one prec
    let y ← div? num den prec
    -- For the atanh-series to converge quickly, we want |y| ≤ 1/2.
    if y.absUpper < (⟨1, -1⟩ : Dyadic) then
      pure ()
    else
      none
    let y2 := mul y y prec
    let tol : Dyadic := ⟨1, prec - 4⟩
    let maxTerms : Nat := (-prec).toNat + 64

    -- log(x) = 2 * atanh(y), where y = (x-1)/(x+1) and atanh(y) = Σ y^(2k+1)/(2k+1).
    let rec loop (fuel : Nat) (t sum : Ball) (k : Nat) : Ball :=
      match fuel with
      | 0 => sum
      | fuel + 1 =>
        let term := divDyadic t ⟨(2 * k + 1 : Int), 0⟩ prec
        let sum' := add sum term prec
        let t' := mul t y2 prec
        let k' := k + 1
        let termNext := divDyadic t' ⟨(2 * k' + 1 : Int), 0⟩ prec
        if termNext.absUpper < tol then
          let tail := (termNext.absUpper * ⟨2, 0⟩).roundUp prec
          { mid := sum'.mid, rad := (sum'.rad + tail).roundUp prec }
        else
          loop fuel t' sum' k'

    let s := loop maxTerms y zero 0
    let ln_x_norm := mul s (ofDyadic ⟨2, 0⟩) prec
    let ln_2 := ln2 prec
    let shift_val := ofDyadic ⟨shift, 0⟩
    let term_shift := mul shift_val (neg ln_2) prec
    pure (add ln_x_norm term_shift prec)

@[inline] private def sinCosSmall (x : Ball) (prec : Int) : Ball × Ball :=
  let x2 := mul x x prec
  let neg_x2 := neg x2
  let tol : Dyadic := ⟨1, prec - 4⟩
  let maxTerms : Nat := (-prec).toNat + 64

  -- sin(x) = Σ (-1)^k x^(2k+1)/(2k+1)!
  let rec sinLoop (fuel : Nat) (term sum : Ball) (k : Nat) : Ball :=
    match fuel with
    | 0 => sum
    | fuel + 1 =>
      let sum' := add sum term prec
      let denom := (2 * k + 2) * (2 * k + 3)
      let term' := divDyadic (mul term neg_x2 prec) ⟨(denom : Int), 0⟩ prec
      if term'.absUpper < tol then
        let tail := term'.absUpper.roundUp prec
        { mid := sum'.mid, rad := (sum'.rad + tail).roundUp prec }
      else
        sinLoop fuel term' sum' (k + 1)

  -- cos(x) = Σ (-1)^k x^(2k)/(2k)!
  let rec cosLoop (fuel : Nat) (term sum : Ball) (k : Nat) : Ball :=
    match fuel with
    | 0 => sum
    | fuel + 1 =>
      let sum' := add sum term prec
      let denom := (2 * k + 1) * (2 * k + 2)
      let term' := divDyadic (mul term neg_x2 prec) ⟨(denom : Int), 0⟩ prec
      if term'.absUpper < tol then
        let tail := term'.absUpper.roundUp prec
        { mid := sum'.mid, rad := (sum'.rad + tail).roundUp prec }
      else
        cosLoop fuel term' sum' (k + 1)

  (sinLoop maxTerms x zero 0, cosLoop maxTerms one zero 0)

@[inline] private def sinCos (x : Ball) (prec : Int) : Ball × Ball :=
  -- Scale down so the Taylor series converges very quickly.
  let u := x.absUpper
  let mag := u.exp + (if u.man = 0 then 0 else u.man.natAbs.log2)
  let k : Int := if mag > -2 then mag + 2 else 0
  let k_nat := k.toNat
  let x_small := x.scale2 (-k)
  let (s0, c0) := sinCosSmall x_small prec

  let two : Ball := ofDyadic ⟨2, 0⟩
  let rec dbl (s c : Ball) : Nat → Ball × Ball
    | 0 => (s, c)
    | n + 1 =>
      let s2 := mul two (mul s c prec) prec
      let c2 := add (mul c c prec) (neg (mul s s prec)) prec
      dbl s2 c2 n

  dbl s0 c0 k_nat

def sin (x : Ball) (prec : Int) : Ball :=
  (sinCos x prec).1

def cos (x : Ball) (prec : Int) : Ball :=
  (sinCos x prec).2

def atan (x : Ball) (prec : Int) : Ball :=
  let quarter : Dyadic := ⟨1, -2⟩ -- 1/4
  let rec reduce (z : Ball) (scale : Nat) (fuel : Nat) : Ball × Nat :=
    match fuel with
    | 0 => (z, scale)
    | fuel + 1 =>
      if z.absUpper < quarter then
        (z, scale)
      else
        let sq := mul z z prec
        let one_plus_sq := add one sq prec
        let root := sqrt one_plus_sq prec
        let den := add one root prec
        match div? z den prec with
        | some z_new => reduce z_new (scale + 1) fuel
        | none => (z, scale)

  let (z_small, scale) := reduce x 0 32

  let z2 := mul z_small z_small prec
  let neg_z2 := neg z2
  let tol : Dyadic := ⟨1, prec - 4⟩
  let maxTerms : Nat := (-prec).toNat + 64

  -- atan(z) = Σ (-1)^k z^(2k+1)/(2k+1)
  -- We keep `powTerm = (-1)^k * z^(2k+1)` (no denominator), and divide by `(2k+1)` when adding.
  let rec loop (fuel : Nat) (powTerm sum : Ball) (k : Nat) : Ball :=
    match fuel with
    | 0 => sum
    | fuel + 1 =>
      let denom := 2 * k + 1
      let term := divDyadic powTerm ⟨(denom : Int), 0⟩ prec
      let sum' := add sum term prec
      let powTerm' := mul powTerm neg_z2 prec
      if term.absUpper < tol then
        let tail := term.absUpper.roundUp prec
        { mid := sum'.mid, rad := (sum'.rad + tail).roundUp prec }
      else
        loop fuel powTerm' sum' (k + 1)

  let res := loop maxTerms z_small zero 0
  mul res (ofDyadic ⟨1, (scale : Int)⟩) prec

def pi (prec : Int) : Ball :=
  let one_fifth := divDyadic one ⟨5, 0⟩ prec
  let one_239 := divDyadic one ⟨239, 0⟩ prec
  let at1 := atan one_fifth prec
  let at2 := atan one_239 prec
  let t1 := mul at1 (ofDyadic ⟨16, 0⟩) prec
  let t2 := mul at2 (ofDyadic ⟨4, 0⟩) prec
  add t1 (neg t2) prec

def tan? (x : Ball) (prec : Int) : Option Ball := do
  let s := sin x prec
  let c := cos x prec
  div? s c prec

end Ball

/-! # 3. FastReal (The Stream) -/

/--
**FastReal**: A function `ℕ → Ball`.
`n` represents the requested precision index (approx bits).
-/
def FastReal := ℕ → Ball

namespace FastReal

def ofDyadic (d : Dyadic) : FastReal := fun _ => Ball.ofDyadic d

instance : Zero FastReal := ⟨fun _ => Ball.zero⟩
instance : One FastReal := ⟨fun _ => Ball.one⟩
instance : Coe Dyadic FastReal := ⟨ofDyadic⟩
instance : OfNat FastReal n := ⟨ofDyadic ⟨n, 0⟩⟩

/--
**Addition**:
To satisfy precision `n`, we calculate at `n+2` to absorb rounding errors,
then round the result to `n`.
-/
def add (x y : FastReal) : FastReal := fun n =>
  let prec := -((n : Int) + 2)
  -- Pull slightly higher precision from inputs
  Ball.add (x (n + 4)) (y (n + 4)) prec

def neg (x : FastReal) : FastReal := fun n =>
  Ball.neg (x n)

/--
**Multiplication**:
We employ a heuristic. We peek at the magnitude of the numbers at low precision
to determine how much extra precision is needed to mask the error scaling.
-/
def mul (x y : FastReal) : FastReal := fun n =>
  -- 1. Peek at magnitude (Index 0)
  let x_mag := (x 0).mid.exp
  let y_mag := (y 0).mid.exp
  -- 2. Dynamic precision adjustment
  -- If numbers are large (exp > 0), we need more bits.
  let guard := Int.natAbs (x_mag + y_mag) + 4
  let lookahead := n + guard
  let prec := -((n : Int) + 2)
  Ball.mul (x lookahead) (y lookahead) prec

def sqrt (x : FastReal) : FastReal := fun n =>
  -- Peek at magnitude
  let x_0 := x 0
  let mag := x_0.mid.exp
  -- If number is small, we need more precision from input
  let extra := if mag < 0 then ((-mag).toNat / 2) + 4 else 2
  let lookahead := n + extra
  let prec := -((n : Int) + 2)
  Ball.sqrt (x lookahead) prec

def exp (x : FastReal) : FastReal := fun n =>
  let lookahead := n + 10
  let prec := -((n : Int) + 2)
  Ball.exp (x lookahead) prec

def sin (x : FastReal) : FastReal := fun n =>
  let lookahead := n + 10
  let prec := -((n : Int) + 2)
  Ball.sin (x lookahead) prec

def cos (x : FastReal) : FastReal := fun n =>
  let lookahead := n + 10
  let prec := -((n : Int) + 2)
  Ball.cos (x lookahead) prec

def atan (x : FastReal) : FastReal := fun n =>
  let x0 := x 0
  let mag := x0.mid.exp
  let extra := if mag > 0 then mag.toNat else 0
  let lookahead := n + 10
  let prec := -((n : Int) + 2 + extra)
  Ball.atan (x lookahead) prec

def pi : FastReal := fun n =>
  let prec := -((n : Int) + 6)
  Ball.pi prec

/-!
### Partial operations

Some operations (reciprocal, division, `log`, `tan`) are **not computable as total functions**
on all computable reals. We therefore expose them as *partial approximators*:
they return `Option Ball` at each requested precision.
-/

/-- Approximate reciprocal; returns `none` if we can't certify separation from `0` at this precision. -/
def inv? (x : FastReal) : ℕ → Option Ball := fun n =>
  let x0 := x 0
  let k := x0.mid.exp
  let extra := if k < 0 then 2 * (-k).toNat else 0
  let lookahead := n + extra + 4
  let prec := -((n : Int) + 2)
  Ball.inv? (x lookahead) prec

/-- Approximate division; returns `none` if we can't certify the denominator is separated from `0`. -/
def div? (x y : FastReal) : ℕ → Option Ball := fun n =>
  let lookahead := n + 10
  let prec := -((n : Int) + 2)
  Ball.div? (x lookahead) (y lookahead) prec

/-- Approximate natural logarithm; returns `none` unless we can certify the input is positive. -/
def log? (x : FastReal) : ℕ → Option Ball := fun n =>
  let lookahead := n + 10
  let prec := -((n : Int) + 2)
  Ball.log? (x lookahead) prec

/-- Approximate logarithm base `b`; returns `none` if either log is undefined or division can't be certified. -/
def logBase? (b x : FastReal) : ℕ → Option Ball := fun n => do
  let prec := -((n : Int) + 2)
  let lx ← log? x n
  let lb ← log? b n
  Ball.div? lx lb prec

/-- Approximate tangent; returns `none` if we can't certify `cos x` is separated from `0`. -/
def tan? (x : FastReal) : ℕ → Option Ball := fun n =>
  let lookahead := n + 10
  let prec := -((n : Int) + 2)
  Ball.tan? (x lookahead) prec

/-!
### Decimal rendering (for `#eval`)

These helpers avoid `Float` and instead render dyadic/rational approximations as decimal strings.
They are intended for debugging / demos, not high-performance numerics.
-/

def ratToDecimal (q : ℚ) (digits : Nat) : String :=
  let sign := if q < 0 then "-" else ""
  let q' : ℚ := if q < 0 then -q else q
  let intPart : Nat := q'.floor.toNat
  let fracPart : ℚ := q' - intPart
  let rec go (k : Nat) (r : ℚ) (acc : String) : String :=
    match k with
    | 0 => acc
    | k + 1 =>
      let r' := 10 * r
      let digit : Nat := r'.floor.toNat
      go k (r' - digit) (acc ++ toString digit)
  sign ++ toString intPart ++ "." ++ go digits fracPart ""

def ballToDecimalMidRad (b : Ball) (digits : Nat) : String :=
  s!"[{ratToDecimal b.mid.toRat digits} ± {ratToDecimal b.rad.toRat digits}]"

def ballToDecimalInterval (b : Ball) (digits : Nat) : String :=
  s!"[{ratToDecimal b.lo.toRat digits}, {ratToDecimal b.hi.toRat digits}]"

def toDecimal (x : FastReal) (digits : Nat := 10) : String :=
  let n := 4 * digits
  ballToDecimalMidRad (x n) digits

def toDecimalInterval (x : FastReal) (digits : Nat := 10) : String :=
  let n := 4 * digits
  ballToDecimalInterval (x n) digits

def abs (x : FastReal) : FastReal := fun n =>
  let prec := -((n : Int) + 2)
  Ball.abs (x n) prec

def pow (x : FastReal) (k : Nat) : FastReal := fun n =>
  if k == 0 then Ball.one
  else
    let x0 := x 0
    let mag := x0.mid.exp
    let extra := if mag > 0 then (k - 1) * mag.toNat else 0
    let lookahead := n + extra + k.log2 + 4
    let prec := -((n : Int) + 2)
    Ball.pow (x lookahead) k prec

def floor (x : FastReal) (fuel : Nat := 100) : Option Int :=
  let rec loop : Nat → Nat → Option Int
    | _, 0 => none
    | i, fuel + 1 =>
      match (x i).floor with
      | some f => some f
      | none => loop (i + 1) fuel
  loop 0 (fuel + 1)

def ceil (x : FastReal) (fuel : Nat := 100) : Option Int :=
  let rec loop : Nat → Nat → Option Int
    | _, 0 => none
    | i, fuel + 1 =>
      match (x i).ceil with
      | some c => some c
      | none => loop (i + 1) fuel
  loop 0 (fuel + 1)

def compare (x y : FastReal) (fuel : Nat := 100) : Option Ordering :=
  let rec loop : Nat → Nat → Option Ordering
    | _, 0 => none
    | i, fuel + 1 =>
      let bx := x i
      let byy := y i
      let x_max := bx.mid + bx.rad
      let x_min := bx.mid - bx.rad
      let y_max := byy.mid + byy.rad
      let y_min := byy.mid - byy.rad
      if x_max < y_min then some Ordering.lt
      else if y_max < x_min then some Ordering.gt
      else loop (i + 1) fuel
  loop 0 (fuel + 1)

def min (x y : FastReal) : FastReal := fun n =>
  let prec := -((n : Int) + 2)
  Ball.min (x n) (y n) prec

def max (x y : FastReal) : FastReal := fun n =>
  let prec := -((n : Int) + 2)
  Ball.max (x n) (y n) prec

def isPos (x : FastReal) (fuel : Nat := 100) : Option Bool :=
  match compare x 0 fuel with
  | some Ordering.gt => some true
  | some _ => some false
  | none => none

def isNeg (x : FastReal) (fuel : Nat := 100) : Option Bool :=
  match compare x 0 fuel with
  | some Ordering.lt => some true
  | some _ => some false
  | none => none

def sign (x : FastReal) (fuel : Nat := 100) : Option Int :=
  match compare x 0 fuel with
  | some Ordering.lt => some (-1)
  | some Ordering.gt => some 1
  | some Ordering.eq => some 0
  | none => none

def hypot (x y : FastReal) : FastReal :=
  sqrt (add (mul x x) (mul y y))

instance : Add FastReal := ⟨add⟩
instance : Sub FastReal := ⟨fun a b => add a (neg b)⟩
instance : Mul FastReal := ⟨mul⟩
instance : Neg FastReal := ⟨neg⟩
instance : Pow FastReal ℕ := ⟨pow⟩
instance : Min FastReal := ⟨min⟩
instance : Max FastReal := ⟨max⟩

instance : SMul ℤ FastReal where
  smul z f := mul (ofDyadic ⟨z, 0⟩) f

-- Pretty printer: Eval at index 20 (~6 decimal digits)
instance : Repr FastReal where
  reprPrec f _ :=
    let b := f 20
    s!"[{b.mid.toFloat} ± {b.rad.toFloat}]"

end FastReal

end Computable.Fast
