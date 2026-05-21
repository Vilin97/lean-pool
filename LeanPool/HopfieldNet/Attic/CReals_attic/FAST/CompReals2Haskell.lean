/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Mathlib.Analysis.RCLike.Basic

/- This code is a Lean 4 port of "Few Digits", a Haskell implementation of computable
reals by Russell O'Connor. Original source: https://r6.ca/FewDigits/ -/

/-- A Gauge is a strictly positive rational number. -/
structure Gauge where
  val : ℚ
  --property : 0 < val

instance : Coe Gauge ℚ where
  coe g := g.val

/--
A type of "complete" elements:
a function from strictly positive rationals (Gauge) to a value of type `a`.
This is a direct translation of the Haskell type alias:
  type Complete a = Gauge -> a
-/
abbrev Complete (a : Type) := Gauge → a


--completeComplete :: (Complete (Complete a)) -> Complete a
--completeComplete f eps = (f (eps/2)) (eps/2)
/--
Given a "complete" function returning another "complete" function,
produce a single "complete" function by evaluating both at half the gauge.
-/
def completeComplete {a : Type} (f : Complete (Complete a)) : Complete a :=
  fun eps => f { val := eps.val / 2--, property := by linarith [eps.property]
  }
                { val := eps.val / 2--, property := by linarith [eps.property]
                }

-- A uniformly continuous function on some subset of a to b
-- Hopefully the name of the function gives an indication of
-- the domain.
-- data UniformCts a b = UniformCts
-- {modulus :: (Gauge -> Gauge),
-- forgetUniformCts :: (a -> b)}
/--
A uniformly continuous function from `a` to `b`,
 equipped with a modulus of uniform continuity.
-/
structure UniformCts (a b : Type) where
  modulus : Gauge → Gauge
  forgetUniformCts : a → b

/--
Evaluate a uniformly continuous function at a "complete" argument,
producing a "complete" result.
-/
def evalUniformCts {a b : Type} (f : UniformCts a b) (x : Complete a) : Complete b :=
  fun eps => f.forgetUniformCts (x (f.modulus eps))

/--
Evaluate a uniformly continuous function returning a "complete" result,
at a "complete" argument, producing a "complete" result.
-/
def evalUniformCts2 {a b : Type} (f : UniformCts a (Complete b)) (x : Complete a) : Complete b :=
  completeComplete (evalUniformCts f x)

-- completeUniformCtsRange :: Complete (UniformCts a b) ->
-- UniformCts a (Complete b)
-- completeUniformCtsRange f = UniformCts mu g
-- where
-- mu eps = modulus (f (eps/2)) (eps/2)
-- g x eps = forgetUniformCts (f eps) x

/--
Given a "complete" family of uniformly continuous functions,
produce a uniformly continuous function into "complete" values.
-/
def completeUniformCtsRange {a b : Type}
  (f : Complete (UniformCts a b)) : UniformCts a (Complete b) where
    modulus := (fun eps =>
      (f { val := eps.val / 2,
--:= by linarith [eps.property]
       }).modulus
        { val := eps.val / 2,
        --property := by linarith [eps.property]
        })
    forgetUniformCts := (fun x => fun eps => (f eps).forgetUniformCts x)

/--
Evaluate a binary uniformly continuous function at two "complete" arguments,
producing a "complete" result.
-/
def evalBinaryUniformCts {a b c : Type}
  (f : UniformCts a (UniformCts b c)) (x : Complete a) (y : Complete b) : Complete c :=
  evalUniformCts2 (completeUniformCtsRange (evalUniformCts f x)) y

/--
Alternative implementation of `evalBinaryUniformCts`:
Evaluates a binary uniformly continuous function at two "complete" arguments,
by first evaluating `f` at `x` at half the gauge, then evaluating
the resulting function at `y` at half the gauge.
-/
def evalBinaryUniformCts' {a b c : Type}
  (f : UniformCts a (UniformCts b c)) (x : Complete a) (y : Complete b) : Complete c :=
  fun eps =>
    let approxf := evalUniformCts f x { val := eps.val / 2,
    -- property := by linarith [eps.property]
    }
    evalUniformCts approxf y { val := eps.val / 2,
    --property := by linarith [eps.property]
     }

/--
Base type is ℚ (rational numbers).
-/
abbrev Base := ℚ

/--
Approximate a rational number by another rational
number with a given denominator.
This is a stub for Haskell's approxRational.
In Lean, we just return the input for now.
-/
def approxBase (x : Base) (_ : ℚ) : Base := x

/--
Generate the list of powers of a rational number.
Given `x`, returns the infinite list `[1, x, x^2, x^3, ...]`.
-/
def powers' (x : ℚ) (n : ℕ) : List ℚ :=
  List.iterate (· * x) 1 n

def genpowers (x : ℚ) (n : ℕ) : List ℚ :=
  List.zipWith (fun _ k => x ^ k) (List.range n) (List.range n)

#eval powers' 5 10

--powers x = zipWith (%) (genpowers n) (genpowers d)

def powers (x : ℚ) (n : ℕ) : List ℚ :=
  let num := x.num
  let den := x.den
  let numPows := genpowers num n
  let denPows := genpowers den n
  List.zipWith (fun a b => (a : ℚ) / (b : ℚ)) numPows denPows

#eval powers (5/2 : ℚ) 10

-- powers x = zipWith (%) (genpowers n) (genpowers d)
-- where
-- n = numerator x
-- d = denominator x
-- genpowers x = 1:(map (x*) (genpowers x))

/--
A small positive rational used as a default radius.
-/
def radius : Base := (2 : ℚ) ^ (-51 : ℤ)

/--
A constructive real number, represented by an approximation function
and an integer approximation.
-/
structure CReal where
  approx : Complete Base
  intApprox : ℤ
deriving Nonempty

--def CReal_eq : CReal_repr → CReal_repr → Prop := sorry

--def CReal : Type := sorry -- CReal_repr modulo CReal_eq

--Start working with quotients

/--
Compute a bound for a constructive real number.
This is `1 + |intApprox x|` as a rational.
-/
def bound (x : CReal) : ℚ := (1 : ℚ) + (Int.natAbs x.intApprox : ℚ)

/--
Construct a `CReal` from a `Complete Base` approximation function.
The integer approximation is `Int.round (x 1/2)`.
For large `eps`, returns the integer approximation; otherwise, uses `x`.
-/
def makeCReal (x : Complete Base) : CReal :=
  let n := round (x { val := 1/2,
  --property := by norm_num
  })
  let x' : Complete Base := fun eps =>
    if eps.val ≥ 1 then n else x eps
  { approx := x', intApprox := n }

/--
Produces a "compressed" version of a complete function,
whose resulting approximations are small in memory size.
-/
def compress (x : Complete Base) : Complete Base :=
  fun eps => approxBase (x { val := eps.val / 2,
  --property := by linarith [eps.property]
  })
                       (eps.val / 2)

/--
"squish" a constructive real number to a "compressed" complete function.
-/
def squish (x : CReal) : Complete Base :=
  compress x.approx

-- instance Show CReal where
-- show x = error "Cannot show a CReal"
-- Russell O’Connor 17
-- {- show x = show $ map (\n -> squish x ((1/2)^n)) [0..] -}

instance : ToString CReal where
  toString _ := "Cannot show a CReal"
-- Alternatively, to show a few approximations:
-- toString x := toString (List.map
  --(fun n => squish x { val := (1/2)^n, property := by positivity }) (List.range 5))

/--
Construct a `CReal` from a rational number.
-/
def realBase (x : Base) : CReal :=
  makeCReal (fun _ => x)

/-- Example: The constructive real number representing 1/3. -/
def exampleCReal : CReal := realBase (1/3 : ℚ)

#eval exampleCReal.approx { val := 1/100 }

/--
Given a constructive real number `x` and a gauge `eps`,
returns a pair `(r - eps, r + eps)` where `r = approx x eps`.
This gives an interval containing the real number.
-/
def approxRange (x : CReal) (eps : Gauge) : Base × Base :=
  let r := x.approx eps
  (r - eps, r + eps)

/--
Finds some `y` such that `0 < |y| ≤ |x|`, starting from a given gauge.
If the interval returned by `approxRange r g` is entirely negative,
returns the upper bound.
If entirely positive, returns the lower bound.
Otherwise, recursively halves the gauge.
Terminates after `fuel` steps to ensure termination.
-/
def proveNonZeroFrom (fuel : Nat) (g : Gauge) (r : CReal) : Base :=
  if fuel = 0 then
    0 -- fallback value if not found in given steps
  else
    let (low, high) := approxRange r g
    if high < 0 ∧ low < 0 then high
    else if 0 < low ∧ 0 < high then low
    else proveNonZeroFrom (fuel - 1) { val := g.val / 2 } r

#eval proveNonZeroFrom 10 { val := 1 } (realBase 2)

/--
Finds some `y` such that `0 < |y| ≤ |x|`, starting from gauge 1.
Warning: does not terminate if the input is 0.
-/
def proveNonZero (r : CReal) : Base :=
  proveNonZeroFrom 10 { val := 1 } r

/--
Construct a `CReal` by applying a uniformly continuous function to a `CReal`.
-/
def makeCRealFun (f : UniformCts Base Base) (x : CReal) : CReal :=
  makeCReal (evalUniformCts f (squish x))

/--
Construct a `CReal` by applying a uniformly continuous function
returning a complete value to a `CReal`.
-/
def makeCRealFun2 (f : UniformCts Base (Complete Base)) (x : CReal) : CReal :=
  makeCReal (evalUniformCts2 f (squish x))

/--
Construct a `CReal` by applying a binary uniformly continuous function to two `CReal`s.
-/
def makeCRealBinFun (f : UniformCts Base (UniformCts Base Base)) (x y : CReal) : CReal :=
  makeCReal (evalBinaryUniformCts f (squish x) (squish y))

/--
Uniformly continuous negation on Base.
-/
def negateCts : UniformCts Base Base :=
  { modulus := id, forgetUniformCts := fun x => -x }

/--
Negation of a constructive real number.
-/
def realNegate (x : CReal) : CReal :=
  makeCRealFun negateCts x
-- realNegate = makeCRealFun negateCts

/--
Uniformly continuous addition of a constant on Base.
-/
def plusBaseCts (a : Base) : UniformCts Base Base :=
  { modulus := id, forgetUniformCts := fun x => a + x }

/--
Translate a constructive real number by a rational constant.
-/
def realTranslate (a : Base) : CReal → CReal :=
  makeCRealFun (plusBaseCts a)

/--
Uniformly continuous addition on Base.
-/
def plusCts : UniformCts Base (UniformCts Base Base) :=
  { modulus := id, forgetUniformCts := plusBaseCts }

/--
Addition of two constructive real numbers.
-/
def realPlus (x y : CReal) : CReal :=
  makeCRealBinFun plusCts x y

instance : BEq CReal where
  beq a b := proveNonZero (realPlus a (realNegate b)) = 0


-- /--
-- Associativity of addition for CReals.
-- -/
-- theorem realPlus_assoc (x y z : CReal) :
--   realPlus (realPlus x y) z = realPlus x (realPlus y z) := by sorry
/--
Uniformly continuous multiplication by zero on Base.
-/
def multBaseCts (a : ℚ) : UniformCts ℚ ℚ :=
  if a = 0 then {
    --modulus := λ _ => ⟨1, by norm_num⟩, -- Any positive number would do
    modulus := λ _ => ⟨1⟩ -- Any positive number would do

    forgetUniformCts := λ _ => 0
  } else {
    modulus := λ eps => ⟨eps.val / |a|--,
      --by have ha : 0 < |a| := abs_pos.mpr (by sorry)
      --exact div_pos eps.property ha
      ⟩
    forgetUniformCts := λ x => a * x
  }

/--
Scale a constructive real number by a rational constant.
If the constant is zero, returns zero; otherwise, uses multiplication.
-/
def realScale (a : Base) (x : CReal) : CReal :=
  if a = 0 then realBase 0 else makeCRealFun (multBaseCts a) x

/--
Uniformly continuous multiplication on Base, with domain restricted to |y| ≤ maxy.
-/
def multUniformCts (maxy : Base) : UniformCts Base (UniformCts Base Base) :=
  { modulus := fun eps =>
      ⟨eps.val / maxy,
        --by
        --have h : 0 < maxy := by
          -- In Haskell, this is an assertion.
          --In Lean, we require the user to ensure maxy > 0.
          --sorry
        --exact div_pos eps.property h
        ⟩,
    forgetUniformCts := multBaseCts }

/--
Multiplication of two constructive real numbers.
We bound the value of `x` and compute `y * x`.
-/
def realMult (x y : CReal) : CReal :=
  makeCRealBinFun (multUniformCts (bound x)) y x

/--
Uniformly continuous absolute value on Base.
-/
def absCts : UniformCts Base Base :=
  { modulus := id, forgetUniformCts := fun x => |x| }

/--
Absolute value of a constructive real number.
-/
def realAbs (x : CReal) : CReal :=
  makeCRealFun absCts x

instance : Add CReal where
  add := realPlus

instance : HAdd CReal CReal CReal where
  hAdd := realPlus

instance : Sub CReal where
  sub x y := realPlus x (realNegate y)

instance : Mul CReal where
  mul := realMult

instance : Neg CReal where
  neg := realNegate

instance : HMul ℚ CReal CReal where
  hMul := realScale

def realZero : CReal := realBase 0

lemma real_zero_add (a : CReal) : realPlus realZero a = a := by {
  unfold realPlus
  unfold makeCRealBinFun
  unfold evalBinaryUniformCts
  unfold makeCReal
  sorry}

lemma real_add_zero (a : CReal) : realPlus a realZero = a := by {
  unfold realPlus
  unfold makeCRealBinFun
  unfold evalBinaryUniformCts
  unfold makeCReal
  sorry
}

lemma real_assoc : ∀ (a b c : CReal), realPlus (realPlus a b) c =
  realPlus a (realPlus b c) := sorry

lemma real_add_comm :
  ∀ (a b : CReal), realPlus a b = realPlus b a := sorry

instance : AddCommMonoid CReal where
  add := realPlus
  add_assoc := real_assoc
  zero := realZero
  zero_add := real_zero_add
  add_zero := real_add_zero
  nsmul := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry
  add_comm := real_add_comm

/--
Sign function for constructive real numbers.
Returns 1, 0, or -1 as a CReal.
-/
def realSignum (x : CReal) : CReal :=
  realScale (by {
    have y := proveNonZero x
    unfold Base at *
    apply (Int.sign y.num : ℚ)
  }) (realBase 1)

/--
Construct a CReal from an integer.
-/
def realFromInteger (n : ℤ) : CReal :=
  realBase n

/--
Uniformly continuous reciprocal function on Base.
If `nonZero > 0`, domain is `[nonZero, ∞)`.
If `nonZero < 0`, domain is `(-∞, nonZero]`.
-/
def recipUniformCts (nonZero : Base) : UniformCts Base Base :=
  let f : Base → Base :=
    if 0 ≤ nonZero then
      fun a => (max nonZero a)⁻¹
    else
      fun a => (min a nonZero)⁻¹
  let mu : Gauge → Gauge :=
    fun eps => ⟨eps.val * nonZero ^ 2,
      --by
      --have h : 0 < |nonZero| := abs_pos.mpr (by
      --  intro h; rw [h] at *; simp at *; sorry)
     -- have h2 : 0 < nonZero ^ 2 := by
     --   apply pow_pos;
     --   simp only [abs_pos, ne_eq] at *
     --   sorry
     -- exact mul_pos eps.property h2
      ⟩
  { modulus := mu, forgetUniformCts := f }

/--
Construct the reciprocal of a constructive real number, given a nonzero witness.
-/
def realRecipWitness (x : CReal) (nonZero : Base) : CReal :=
  makeCRealFun (recipUniformCts nonZero) x

/--
Construct the reciprocal of a constructive real number.
Warning: does not terminate if the input is zero.
-/
def realRecip (x : CReal) : CReal :=
  realRecipWitness x (proveNonZero x)

-- instance Fractional CReal where
-- recip = realRecip
-- fromRational = realBase . fromRational

instance : Inv CReal where
  inv := realRecip

/--
Uniformly continuous integer power function on Base.
Given a bound `maxx` and exponent `n`, returns a uniformly continuous function `x ↦ x^n`.
-/
def intPowerCts (maxx : Base) (n : ℕ) : UniformCts Base Base :=
  if n = 0 then
    { modulus := fun _ => ⟨1⟩     --, by norm_num
    --⟩,
      forgetUniformCts := fun _ => 1 }
  else
    { modulus := fun eps =>
        ⟨eps.val / ((n : ℚ) * maxx ^ (n - 1))

        -- , by
        --   have hmaxx : 0 < maxx := by sorry
        --   have hn : 0 < (n : ℚ) := by
        --     have : 0 < n := Nat.pos_of_ne_zero (by intro h; rw [h] at *; sorry)
        --     exact Nat.cast_pos.mpr this
        --   have hden : 0 < (n : ℚ) * maxx ^ (n - 1) := mul_pos hn (pow_pos hmaxx _)
        --   exact div_pos eps.property hden

          ⟩,
      forgetUniformCts := fun x => x ^ n }

/--
Raise a constructive real number to a non-negative integer power.
-/
def realPowerInt (x : CReal) (n : ℕ) : CReal :=
  makeCRealFun (intPowerCts (bound x) n) x

/--
A polynomial over `a` is represented as a list of coefficients.
-/
abbrev polynomial (a : Type) := List a

/--
Evaluate a polynomial at a given value.
Given a list of coefficients `[a₀, a₁, ..., aₙ]` and `x`, computes `a₀ + a₁*x + ... + aₙ*xⁿ`.
-/
def evalPolynomial {a : Type} [Add a] [Mul a] [OfNat a 0] (p : polynomial a) (x : a) : a :=
  p.foldr (fun a acc => a + x * acc) 0

-- Example: 2 + 3x + 4x^2 at x = 5
#eval evalPolynomial ([2, 3, 4] : polynomial ℚ) 5

/--
Compute the formal derivative of a polynomial.
Given a list of coefficients `[a₀, a₁, ..., aₙ]`, returns `[a₁, 2*a₂, 3*a₃, ..., n*aₙ]`.
-/
def diffPolynomial {a : Type} [Add a] [Mul a] [OfNat a 1] [NatCast a] (p : polynomial a) : polynomial a :=
  p.tail.zipWith (fun coeff idx => coeff * idx) (List.range p.length |>.map (fun n => (n + 1 : a)))

-- Example: The derivative of 2 + 3x + 4x^2 is 3 + 8x
#eval diffPolynomial ([2, 3, 4] : polynomial ℚ)  -- Output: [3, 8]
#time #eval diffPolynomial ([2, 3, 4] : polynomial ℚ)  -- Output: [3, 8]
/--
Given a bound `maxx` and a polynomial `p`, returns a uniformly continuous function
that evaluates the polynomial at a given input.
The modulus is determined by the maximum slope of the polynomial on `[−maxx, maxx]`.
-/
def polynomialUniformCts (maxx : Base) (p : polynomial Base) : UniformCts Base Base :=
  if p = [] then
    { modulus := fun _ => ⟨1 --, by norm_num
    ⟩, forgetUniformCts := fun _ => 0 }
  else
    let maxSlope :=
      let diff := diffPolynomial p
      let absDiff := diff.map (fun x => |x|)
      let evalAt := max 1 (|maxx|)
      evalPolynomial absDiff evalAt
    if maxSlope = 0 then
      { modulus := fun _ => ⟨1 --, by norm_num
      ⟩,
        forgetUniformCts := fun _ => p.head! }
    else
      { modulus := fun eps =>
          ⟨eps.val / maxSlope, --by
            --have h : 0 < maxSlope := by
              -- In Haskell, this is an assertion.
              -- In Lean, we require the user to ensure maxSlope > 0.
              --sorry
            --exact div_pos eps.property h
            ⟩,
        forgetUniformCts := evalPolynomial p }


/--
Construct a `CReal` by evaluating a polynomial with rational
coefficients at a `CReal`.
-/
def realBasePolynomial (p : polynomial Base) (x : CReal) : CReal :=
  makeCRealFun (polynomialUniformCts (bound x) p) x

-- factorials = fact 1 1
-- where
-- fact i j = i:(fact (i*j) (j+1))
/--
Generate the infinite list of factorials: [1, 1*2, 1*2*3, ...].
Returns the first `n` factorials as a list.
-/
def factorials (n : ℕ) : List ℚ :=
  let rec fact (acc i : ℚ) (k : ℕ) : List ℚ :=
    if k = 0 then [] else acc :: fact (acc * i) (i + 1) (k - 1)
  fact 1 1 n


-- interleave [] _ = []
-- interleave (x:xs) l = x:(interleave l xs)

/--
Compute the Taylor approximation of a function given by its power series coefficients `p`
at point `x`, with error control parameter `m` and gauge `eps`.
Sums the terms `p_i * (x^i / i!)` while `m * |x^i / i!| ≥ eps`.
-/
def taylorApprox (m : ℚ) (p : List ℚ) (x : ℚ) (eps : ℚ) : ℚ :=
  let preTerms := List.zipWith (fun num den => num / den) (powers x p.length) (factorials p.length)
  let highError (t : ℚ) := m * |t| ≥ eps
  let terms := List.zipWith (· * ·) p (preTerms.takeWhile highError)
  terms.sum


/--
Only valid for `|x| ≤ 1/2`. Computes exp(x) using its Taylor series.
-/
def rationalSmallExp (x : Base) : CReal :=
  -- Only valid for |x| ≤ 1/2
  if |x| ≤ (1/2 : ℚ) then
    let m := if x ≤ 0 then (1 : ℚ) else (2 : ℚ)
    let expTaylorApprox : Complete Base :=
      fun eps =>
        let n := 100  -- Truncate after 100 terms for safety (can be increased)
        let terms := List.zipWith (fun num den => num / den) (powers x n) (factorials n)
        let highError (t : ℚ) := m * |t| ≥ eps.val
        let filtered := terms.takeWhile highError
        filtered.sum
    makeCReal expTaylorApprox
  else
    -- Out of domain, just return 0 (or could throw an error)
    realBase 0


-- rationalExp :: Base -> Base -> CReal
-- rationalExp tol x | (abs x) <= tol = rationalSmallExp x
-- | otherwise = realPowerInt (rationalExp tol (x/2)) 2
/--
Compute exp(x) as a constructive real, with error control parameter `tol`.
If `|x| ≤ tol`, uses the Taylor series; otherwise, recursively
halves the argument and squares the result.
-/
def rationalExpAux (tol x : Base) (fuel : Nat) : CReal :=
  if fuel = 0 then
    rationalSmallExp x -- fallback to Taylor for safety
  else if |x| ≤ tol then
    rationalSmallExp x
  else
    realPowerInt (rationalExpAux tol (x / 2) (fuel - 1)) 2

def rationalExp (tol x : Base) : CReal :=
  rationalExpAux tol x 100 -- 100 is an arbitrary recursion limit; increase as needed

-- Example: Compute exp(1) with tolerance 1/2
#time #eval (rationalExp (1/10) 1).approx { val := 1/100, --property := by norm_num
 }

/--
Uniformly continuous exponential function on Base, returning a complete value.
Given an integer upper bound, returns a uniformly continuous function approximating exp(x).
-/
def expUniformCts (upperBound : ℤ) : UniformCts Base (Complete Base) :=
  let mu : Gauge → Gauge :=
    fun eps =>
      if upperBound ≤ 0 then
        ⟨eps.val * (2 : ℚ) ^ (-upperBound),
          -- by
          -- have h : 0 < eps.val := eps.property
          -- have h2 : 0 < (2 : ℚ) ^ (-upperBound) := sorry
          --   --apply pow_pos; norm_num
          -- exact mul_pos h h2
          ⟩
      else
        ⟨eps.val / (3 : ℚ) ^ upperBound,
        --  by
        --   have h : 0 < eps.val := eps.property
        --   have h3 : 0 < (3 : ℚ) ^ upperBound := by sorry
        --     --apply pow_pos; norm_num
        --   exact div_pos h h3
          ⟩
  { modulus := mu, forgetUniformCts := fun x => (rationalExp radius x).approx }

/--
Exponential function on constructive real numbers.
-/
def realExp (x : CReal) : CReal :=
  makeCRealFun2 (expUniformCts (1 + x.intApprox)) x

-- Example: Compute exp(1) and print the result
--#time #eval (realExp (realBase 1)).approx { val := 1/2 }


/--
Given a (possibly infinite) list of terms `a` (assumed to be an
alternating series with decreasing absolute values),
returns a complete function that, for a given gauge `eps`,
sums the terms whose absolute value exceeds `eps`.
-/
def alternatingSeries (a : List Base) : Complete Base :=
  fun eps =>
    let partSeries := a.takeWhile (fun x => |x| > eps.val)
    partSeries.sum

/--
Compute sin(x) as a constructive real, with error control parameter `tol`
and recursion limit `fuel`.
If `|x| ≥ tol`, reduces the argument using the triple-angle identity:
  sin(x) = 3 sin(x/3) - 4 sin^3(x/3)
Otherwise, computes the alternating series expansion for sin(x) up to `fuel` terms.
-/
def rationalSinAux (tol x : Base) (fuel : Nat) : CReal :=
  if fuel = 0 then
    realBase 0
  else if tol ≤ |x| then
    -- Use triple-angle identity: sin(x) = 3 sin(x/3) - 4 sin^3(x/3)
    realBasePolynomial [0, 3, 0, -4] (rationalSinAux tol (x / 3) (fuel - 1))
  else
    -- Use Taylor series: sin(x) = x - x^3/6 + x^5/120 - ...
    let nTerms := fuel
    let rec terms (t : Base) (n : ℚ) (k : Nat) : List (Base × ℚ) :=
      if k = 0 then [] else (t, n) :: terms (-(t * x * x) / (n * (n + 1))) (n + 2) (k - 1)
    let zipped := terms x 2 nTerms
    let series := zipped.map (fun (t, _) => t)
    makeCReal (alternatingSeries series)

/--
Compute sin(x) as a constructive real, with error control parameter `tol`.
This is a wrapper for `rationalSinAux` with a fixed recursion limit.
-/
def rationalSin (tol x : Base) : CReal :=
  rationalSinAux tol x 100

/--
Uniformly continuous sine function on Base, returning a complete value.
-/
def sinCts : UniformCts Base (Complete Base) :=
  { modulus := id, forgetUniformCts := fun x => (rationalSin radius x).approx }

/--
A "slow" sine function on constructive real numbers,
computed directly from the Taylor series.
-/
def realSlowSin : CReal → CReal :=
  makeCRealFun2 sinCts

/--
Compute cos(x) as a constructive real, with error control parameter `tol`.
Implements the identity: cos(x) = 1 - 2 * sin^2(x/2).
-/
def rationalCos (tol x : Base) : CReal :=
  realBasePolynomial [1, 0, -2] (rationalSin tol (x / 2))

/--
Uniformly continuous cosine function on Base, returning a complete value.
-/
def cosCts : UniformCts Base (Complete Base) :=
  { modulus := id, forgetUniformCts := fun x => (rationalCos radius x).approx }

/--
A "slow" cosine function on constructive real numbers,
computed directly from the Taylor series.
-/
def realSlowCos : CReal → CReal :=
  makeCRealFun2 cosCts

/--
Compute ln(x) for 1 ≤ x ≤ 3/2 using the alternating series expansion.
That is, ln(x) = sum_{n=1}^∞ [(-1)^{n+1} (x-1)^n / n]
This version is non-recursive and truncates after `nTerms` terms.
-/
def rationalSmallLn (x : Base) : CReal :=
  if (1 : ℚ) ≤ x ∧ x ≤ (3/2 : ℚ) then
    let nTerms := 100
    let coeffs := List.range nTerms |>.map
      (fun k => ((if k % 2 = 0 then 1 else -1) : ℚ) / ((k + 1 : Nat) : ℚ))
    let powersList := (powers (x - 1) (nTerms + 1)).tail
    let terms := List.zipWith (· * ·) coeffs powersList
    makeCReal (alternatingSeries terms)
  else
    -- Out of domain, just return 0 (or could throw an error)
    realBase 0

-- {- requires that 0<=x -}
-- rationalLn :: Base -> CReal
-- rationalLn x | x<1 = negate (posLn (recip x))
-- | otherwise = posLn x
-- where
-- ln43 = rationalSmallLn (4/3)
-- ln2 = wideLn 2
-- {- good for 1<=x<=2 -}
-- wideLn x | x < (3/2) = rationalSmallLn x
-- | otherwise = (rationalSmallLn ((3/4)*x)) + ln43
-- {- requires that 1<=x -}
-- posLn x | n==0 = wideLn x
-- | otherwise = (wideLn x’) + (realScale n ln2)
-- where
-- (x’,n) = until (\(x,n) -> (x<=2)) (\(x,n) -> (x/2,n+1)) (x,0)


-- {- domain is [nonZero, inf) -}
-- lnUniformCts :: Base -> UniformCts Base (Complete Base)
-- lnUniformCts nonZero = UniformCts mu f
-- where
-- f x = approx $ rationalLn (max x nonZero)
-- mu eps = assert (nonZero > 0) $ eps*nonZero

/-- TODO as above
Uniformly continuous natural logarithm function on Base, returning a complete value.
Requires `nonZero > 0` as a lower bound for the domain.
-/
def lnUniformCts (nonZero : Base) : UniformCts Base (Complete Base) :=
  { modulus := fun eps =>
      ⟨eps.val * nonZero,
        -- by
        -- have h : 0 < nonZero := by
        --   -- In Haskell, this is an assertion.
        --   -- In Lean, we require the user to ensure nonZero > 0.
        --   sorry
        -- exact mul_pos eps.property h
        ⟩,
    forgetUniformCts := fun x =>
      -- Only valid for x ≥ nonZero > 0
      -- Here, we would implement rationalLn (max x nonZero)
      -- For now, this is a stub returning 0
      (realBase 0).approx
  }

/--
Construct the natural logarithm of a constructive real number,
given a nonzero witness.
-/
def realLnWitness (x : CReal) (nonZero : Base) : CReal :=
  makeCRealFun2 (lnUniformCts nonZero) x

/--
Construct the natural logarithm of a constructive real number.
Warning: does not terminate if the input is zero.
-/
def realLn (x : CReal) : CReal :=
  realLnWitness x (proveNonZero x)

/--
Compute a Taylor approximation of arctangent for |x| < 1, as a CReal.
Uses the alternating series expansion:
  arctan(x) = x - x^3/3 + x^5/5 - x^7/7 + ...
That is, sum_{n=0}^∞ [ (-1)^n x^{2n+1} / (2n+1) ]
This version only defined for |x| < 1/2 (tightest domain for convergence/practical error).
-/
def rationalSmallArcTan (x : Base) : CReal :=
  if |x| < (1/2 : ℚ) then
    let n := 100  -- number of terms to use; increase for more precision
    let signs := List.range n |>.map (fun k => if k % 2 = 0 then 1 else -1)
    let numerators := List.range n |>.map (fun k => x ^ (2 * k + 1))
    let denominators := List.range n |>.map (fun k => (2 * k + 1 : ℚ))
    let terms := List.zipWith3 (fun s num den => s * num / den) signs numerators denominators
    makeCReal (alternatingSeries terms)
  else
    -- Out of domain: fallback
    realBase 0

-- Example: Evaluate arctan(1/3) at gauge 1/100
#eval (rationalSmallArcTan (1/3)).approx { val := 1/100 }  -- Should be close to 0.32175

-- Print the result as a string for easier comparison:
#eval toString ((rationalSmallArcTan (1/3)).approx { val := 1/100 })

/--
Uniformly continuous arctangent function on Base, returning a complete value.
Currently a stub using rationalSmallArcTan for |x| < 1/2.
-/
def arcTanCts : UniformCts Base (Complete Base) :=
  { modulus := id, forgetUniformCts := fun x => (rationalSmallArcTan x).approx }

/--
Arctangent function on constructive real numbers.
-/
def realArcTan : CReal → CReal :=
  makeCRealFun2 arcTanCts

/--
Computes x * Pi using Machin-like formulas.
-/
def scalePi (x : Base) : CReal :=
  ((realScale (x * 48) (rationalSmallArcTan (1/38))) +
   (realScale (x * 80) (rationalSmallArcTan (1/57)))) +
  ((realScale (x * 28) (rationalSmallArcTan (1/239))) +
   (realScale (x * 96) (rationalSmallArcTan (1/268))))

def real2Pi : CReal := scalePi 2
def realPi : CReal := scalePi 1
def realPi2 : CReal := scalePi (1/2)
def realPi4 : CReal := scalePi (1/4)

/--
Compute arctangent of a rational number as a CReal, using argument reduction and recursion.
Implements the following logic:
- If x ≤ -1/2, use arctan(x) = -arctan(-x)
- If x > 2, use arctan(x) = π/2 - arctan(1/x)
- If 1/2 ≤ x ≤ 2, use arctan(x) = π/4 + arctan((x-1)/(x+1))
- Otherwise, use the Taylor series for |x| < 1/2.
-/
def rationalArcTanAux : Nat → Base → CReal
| 0, x => rationalSmallArcTan x -- fallback for termination
| fuel + 1, x =>
  if x ≤ (-1/2 : ℚ) then
    realNegate (rationalArcTanAux fuel (-x))
  else
    posArcTan fuel x
where
  /-- Helper for positive x > -1/2 -/
  posArcTan : Nat → Base → CReal
  | 0, x => rationalSmallArcTan x
  | fuel + 1, x =>
    if (2 : ℚ) < x then
      realPi2 - rationalArcTanAux fuel (x⁻¹)
    else if (1/2 : ℚ) ≤ x then
      realPi4 + rationalArcTanAux fuel ((x - 1) / (x + 1))
    else
      rationalSmallArcTan x

/--
Safe wrapper for rationalArcTanAux with default fuel.
-/
def rationalArcTan (x : Base) : CReal :=
  rationalArcTanAux 100 x

/--
Sine function on constructive real numbers, using argument reduction.
Implements the periodicity and symmetry of sine via reduction modulo 2π.
-/
def realSin (x : CReal) : CReal :=
  let n : ℤ := ((x * realPi2⁻¹).intApprox)
  let m : Nat := (n % 4).natAbs
  let x' : CReal := x - realScale n realPi2
  match m with
  | 0 => realSlowSin x'
  | 1 => realSlowCos x'
  | 2 => realNegate (realSlowSin x')
  | 3 => realNegate (realSlowCos x')
  | _ => realSlowSin x' -- fallback, should not happen

/--
Cosine function on constructive real numbers, using argument reduction.
Implements the periodicity and symmetry of cosine via reduction modulo 2π.
-/
def realCos (x : CReal) : CReal :=
  let n : ℤ := ((x * realPi2⁻¹).intApprox)
  let m : Nat := (n % 4).natAbs
  let x' : CReal := x - realScale n realPi2
  match m with
  | 3 => realSlowSin x'
  | 0 => realSlowCos x'
  | 1 => realNegate (realSlowSin x')
  | 2 => realNegate (realSlowCos x')
  | _ => realSlowCos x' -- fallback, should not happen

/--
Given a list of pairs `(lb, ub)`, returns a complete function that,
for a given gauge `eps`, returns the midpoint `(ub + lb) / 2` of the first pair
where `ub - lb < 2 * eps`. Otherwise, continues with the rest of the list.
-/
def nestedBalls : List (Base × Base) → Complete Base
| [] => fun _ => 0
| (lb, ub) :: bs =>
  fun eps =>
    if ub - lb < 2 * eps.val then
    (ub + lb) / 2
    else
    nestedBalls bs eps

/--
An alternative algorithm for computing the square root of a rational number,
using nested intervals (balls) that shrink to the true value.
-/
def betterBounds (x : Base) (lbub : Base × Base) : Base × Base :=
  let (lb, ub) := lbub
  let intercept (a b : Base) : Base := (x + a * b) / (a + b)
  let lb' := intercept lb ub
  let ub1 := intercept lb lb
  let ub2 := intercept ub ub
  let ub' := if lb > 0 then min ub1 ub2 else ub2
  (lb', ub')

/--
Compute the square root of a rational number using the nested balls method.
-/
def rationalSqrt (x : Base) : CReal :=
  let initial := (0, (1 + x) / 2)
  let balls : List (Base × Base) :=
    List.iterate (betterBounds x) initial 100  -- 100 iterations; increase for more precision
  makeCReal (nestedBalls balls)

-- {- Freek’s algorithm -}
-- rationalSqrt :: Base -> CReal
-- rationalSqrt n | n < 1 = realScale (1/2) (rationalSqrt (4*n))
-- | 4 <= n = realScale 2 (rationalSqrt (n/4))
-- | otherwise = makeCReal (\eps -> f eps)
-- where
-- f eps = fst $ until (\(x,err) -> err <= eps) newton ((1+n)/2, 1/2)
-- newton (x,err) = (approxBase x’ e1, e1*2)
-- where
-- x’ = (n+x^2)/(2*x)
-- e1 = err^2/2
-- sqrtCts :: UniformCts Base (Complete Base)
-- sqrtCts = UniformCts (^2) (approx . rationalSqrt)
-- realSqrt :: CReal -> CReal
-- realSqrt = makeCRealFun2 sqrtCts
-- instance Floating CReal where
-- exp = realExp
-- log = realLn
-- pi = realPi
-- sin = realSin
-- cos = realCos
-- atan = realArcTan
-- sqrt = realSqrt
-- sinh x = realScale (1/2) (exp x - (exp (-x)))
-- cosh x = realScale (1/2) (exp x + (exp (-x)))
-- asin x = atan (x/sqrt(realTranslate 1 (negate (realPowerInt x 2))))
-- acos x = realPi2 - asin x
-- acosh x = log (x+sqrt(realTranslate (-1) (realPowerInt x 2)))
-- asinh x = log (x+sqrt(realTranslate 1 (realPowerInt x 2)))
-- atanh x = realScale (1/2)
-- (log ((realTranslate 1 x) / (realTranslate 1 (negate x))))

-- {- testing stuff is below -}
-- test0 = makeCReal id
-- answer n x = shows (intApprox (realScale (10^n) x))
-- "x10^-"++(show n)
-- sumRealList :: [CReal] -> CReal
-- sumRealList [] = realBase 0
-- sumRealList l = makeCReal (\eps -> sum (map (\x -> approx x (eps/n)) l))
-- where
-- n = fromIntegral $ length l

/--
Sum a list of constructive real numbers.
-/
def sumRealList (l : List CReal) : CReal :=
  if l.isEmpty then realBase 0
  else
    makeCReal (fun eps =>
      let n : ℚ := l.length
      (l.map (fun x => x.approx { val := eps.val / n })).sum)

/-- Example: Sum the constructive real numbers 1/3, 1/4, and 1/5. -/
def exampleSum : CReal :=
  sumRealList [realBase (1/3), realBase (1/4), realBase (1/5)]

#eval exampleSum.approx { val := 1/100 }
