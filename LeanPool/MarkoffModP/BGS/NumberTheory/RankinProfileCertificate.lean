/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.NumberTheory.TruncatedOrderTotientRankinFactorization

/-!
# Certificates for neighboring Rankin profiles

Define rational weight caps and finite profile checks, and connect the Boolean checks with their
mathematical validity predicates.
-/

@[expose] public section

namespace BGS.NumberTheory

structure RationalPrimeWeightCap where
  lowerPrime : ℕ
  numerator : ℕ
  denominator : ℕ
  deriving DecidableEq, Repr

namespace RationalPrimeWeightCap

def weight (cap : RationalPrimeWeightCap) : ℚ :=
  cap.numerator / cap.denominator

def Valid (cap : RationalPrimeWeightCap) : Prop :=
  0 < cap.lowerPrime ∧
  0 < cap.numerator ∧
  0 < cap.denominator ∧
  cap.denominator ^ 12 ≤ cap.lowerPrime * cap.numerator ^ 12

def check (cap : RationalPrimeWeightCap) : Bool :=
  decide (0 < cap.lowerPrime) &&
  decide (0 < cap.numerator) &&
  decide (0 < cap.denominator) &&
  decide (cap.denominator ^ 12 ≤
    cap.lowerPrime * cap.numerator ^ 12)

@[simp] theorem check_eq_true_iff (cap : RationalPrimeWeightCap) :
    cap.check = true ↔ cap.Valid := by
  simp [check, Valid, and_assoc]

theorem weight_nonneg (cap : RationalPrimeWeightCap) :
    0 ≤ cap.weight := by
  exact div_nonneg (by positivity) (by positivity)

theorem one_le_prime_mul_weight_pow_twelve
    (cap : RationalPrimeWeightCap) (hcap : cap.Valid)
    {prime : ℕ} (hfloor : cap.lowerPrime ≤ prime) :
    1 ≤ (prime : ℚ) * cap.weight ^ 12 := by
  have hnat :
      cap.denominator ^ 12 ≤ prime * cap.numerator ^ 12 := by
    exact hcap.2.2.2.trans (Nat.mul_le_mul_right _ hfloor)
  have hdenPos : (0 : ℚ) < cap.denominator ^ 12 := by
    have : (0 : ℚ) < cap.denominator := by
      exact_mod_cast hcap.2.2.1
    positivity
  rw [weight, div_pow]
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hdenPos).2
  rw [one_mul]
  exact_mod_cast hnat

end RationalPrimeWeightCap

/-- Which neighboring group order, `p - 1` or `p + 1`, contains an odd
prime-power factor. -/
inductive NeighborSide where
  | minus
  | plus
  deriving DecidableEq, Repr

/-- One globally ordered odd-prime slot in a joint factorization profile. -/
structure RankinOddFactor where
  side : NeighborSide
  exponent : ℕ
  weightCap : RationalPrimeWeightCap
  deriving DecidableEq, Repr

namespace RankinOddFactor

def Valid (factor : RankinOddFactor) : Prop :=
  0 < factor.exponent ∧
  factor.weightCap.Valid ∧
  factor.weightCap.lowerPrime.Prime ∧
  3 ≤ factor.weightCap.lowerPrime

def check (factor : RankinOddFactor) : Bool :=
  decide (0 < factor.exponent) &&
  factor.weightCap.check &&
  decide factor.weightCap.lowerPrime.Prime &&
  decide (3 ≤ factor.weightCap.lowerPrime)

@[simp] theorem check_eq_true_iff (factor : RankinOddFactor) :
    factor.check = true ↔ factor.Valid := by
  simp [check, Valid, and_assoc]

end RankinOddFactor

def allRankinOddFactorsValid : List RankinOddFactor → Prop
  | [] => True
  | factor :: factors =>
      factor.Valid ∧ allRankinOddFactorsValid factors

def allRankinOddFactorsCheck : List RankinOddFactor → Bool
  | [] => true
  | factor :: factors =>
      factor.check && allRankinOddFactorsCheck factors

@[simp] theorem allRankinOddFactorsCheck_eq_true_iff
    (factors : List RankinOddFactor) :
    allRankinOddFactorsCheck factors = true ↔
      allRankinOddFactorsValid factors := by
  induction factors with
  | nil => simp [allRankinOddFactorsCheck, allRankinOddFactorsValid]
  | cons factor factors ih =>
      simp [allRankinOddFactorsCheck, allRankinOddFactorsValid, ih]

def rankinOddFloorsStrictlyIncreasing
    (factors : List RankinOddFactor) : Prop :=
  factors.Pairwise fun left right =>
    left.weightCap.lowerPrime < right.weightCap.lowerPrime

def rankinOddFloorsStrictlyIncreasingCheck :
    List RankinOddFactor → Bool
  | [] => true
  | factor :: factors =>
      factors.all (fun later =>
        decide (factor.weightCap.lowerPrime <
          later.weightCap.lowerPrime)) &&
        rankinOddFloorsStrictlyIncreasingCheck factors

@[simp] theorem rankinOddFloorsStrictlyIncreasingCheck_eq_true_iff
    (factors : List RankinOddFactor) :
    rankinOddFloorsStrictlyIncreasingCheck factors = true ↔
      rankinOddFloorsStrictlyIncreasing factors := by
  induction factors with
  | nil =>
      simp [rankinOddFloorsStrictlyIncreasingCheck,
        rankinOddFloorsStrictlyIncreasing]
  | cons factor factors ih =>
      simp [rankinOddFloorsStrictlyIncreasingCheck,
        rankinOddFloorsStrictlyIncreasing, ih]

/-- The two-adic data and globally sorted odd support of a possible pair
`p - 1`, `p + 1`. -/
structure RankinNeighborProfile where
  minusTwoExponent : ℕ
  plusTwoExponent : ℕ
  twoWeightCap : RationalPrimeWeightCap
  oddFactors : List RankinOddFactor
  rootCap : ℕ
  deriving DecidableEq, Repr

namespace RankinNeighborProfile

def twoExponent
    (profile : RankinNeighborProfile) : NeighborSide → ℕ
  | .minus => profile.minusTwoExponent
  | .plus => profile.plusTwoExponent

def oddDivisorCount : NeighborSide → List RankinOddFactor → ℕ
  | _, [] => 1
  | side, factor :: factors =>
      (if factor.side = side then factor.exponent + 1 else 1) *
        oddDivisorCount side factors

def divisorCount
    (profile : RankinNeighborProfile) (side : NeighborSide) : ℕ :=
  (profile.twoExponent side + 1) *
    oddDivisorCount side profile.oddFactors

def jointDivisorCount (profile : RankinNeighborProfile) : ℕ :=
  profile.divisorCount .minus + profile.divisorCount .plus

def oddCoarseEulerProduct :
    NeighborSide → List RankinOddFactor → ℚ
  | _, [] => 1
  | side, factor :: factors =>
      (if factor.side = side then
          coarseRankinPrimePowerFactor factor.exponent
            factor.weightCap.weight
        else 1) *
        oddCoarseEulerProduct side factors

def coarseEulerProduct
    (profile : RankinNeighborProfile) (side : NeighborSide) : ℚ :=
  coarseRankinPrimePowerFactor (profile.twoExponent side)
      profile.twoWeightCap.weight *
    oddCoarseEulerProduct side profile.oddFactors

def jointCoarseEulerProduct (profile : RankinNeighborProfile) : ℚ :=
  profile.coarseEulerProduct .minus +
    profile.coarseEulerProduct .plus

/-- Product lower bound contributed by the odd factors assigned to one side. -/
def oddLowerNeighborProduct :
    NeighborSide → List RankinOddFactor → ℕ
  | _, [] => 1
  | side, factor :: factors =>
      (if factor.side = side then
          factor.weightCap.lowerPrime ^ factor.exponent
        else 1) *
        oddLowerNeighborProduct side factors

/-- Factorization lower bound for `p - 1` or `p + 1` represented by a
profile.  Unlike the failure square, this grows exponentially in large exact
exponents and will support sound branch exclusion. -/
def lowerNeighborProduct
    (profile : RankinNeighborProfile) (side : NeighborSide) : ℕ :=
  2 ^ profile.twoExponent side *
    oddLowerNeighborProduct side profile.oddFactors

def witnessCap (profile : RankinNeighborProfile) : ℕ :=
  189 * profile.jointDivisorCount ^ 3

/-- Structural and arithmetic validity of one complete profile payload. -/
def Valid (profile : RankinNeighborProfile) : Prop :=
  ((profile.minusTwoExponent = 1 ∧
      2 ≤ profile.plusTwoExponent) ∨
    (profile.plusTwoExponent = 1 ∧
      2 ≤ profile.minusTwoExponent)) ∧
  profile.twoWeightCap.Valid ∧
  profile.twoWeightCap.lowerPrime = 2 ∧
  allRankinOddFactorsValid profile.oddFactors ∧
  rankinOddFloorsStrictlyIncreasing profile.oddFactors ∧
  0 < profile.rootCap ∧
  profile.witnessCap ≤ profile.rootCap ^ 12

/-- A profile closes a proposed cutoff when its rational failure square lies
strictly below `8 * (cutoff + 1)`. -/
def failureSquare (profile : RankinNeighborProfile) : ℚ :=
  ((profile.witnessCap : ℚ) * profile.rootCap *
    profile.jointCoarseEulerProduct) ^ 2

def ClosesCutoff
    (profile : RankinNeighborProfile) (cutoff : ℕ) : Prop :=
  profile.failureSquare < (8 * (cutoff + 1) : ℕ)

/-- A profile excludes the failure obstruction when one represented
neighboring product already forces `p` above the profile failure square. -/
def ExcludesFailure (profile : RankinNeighborProfile) : Prop :=
  profile.failureSquare <
      (8 * (profile.lowerNeighborProduct .minus + 1) : ℕ) ∨
    profile.failureSquare <
      (8 * (profile.lowerNeighborProduct .plus - 1) : ℕ) ∨
    profile.failureSquare ^ 2 <
      (64 * (profile.lowerNeighborProduct .minus *
        profile.lowerNeighborProduct .plus) : ℕ)

def check (profile : RankinNeighborProfile) : Bool :=
  (decide
      ((profile.minusTwoExponent = 1 ∧
          2 ≤ profile.plusTwoExponent) ∨
        (profile.plusTwoExponent = 1 ∧
          2 ≤ profile.minusTwoExponent))) &&
    profile.twoWeightCap.check &&
    decide (profile.twoWeightCap.lowerPrime = 2) &&
    allRankinOddFactorsCheck profile.oddFactors &&
    rankinOddFloorsStrictlyIncreasingCheck profile.oddFactors &&
    decide (0 < profile.rootCap) &&
    decide (profile.witnessCap ≤ profile.rootCap ^ 12)

def closesCutoffCheck
    (profile : RankinNeighborProfile) (cutoff : ℕ) : Bool :=
  decide
    ((((profile.witnessCap : ℚ) * profile.rootCap *
        profile.jointCoarseEulerProduct) ^ 2) <
      ((8 * (cutoff + 1) : ℕ) : ℚ))

def excludesFailureCheck (profile : RankinNeighborProfile) : Bool :=
  decide
    (profile.failureSquare <
        ((8 * (profile.lowerNeighborProduct .minus + 1) : ℕ) : ℚ) ∨
      profile.failureSquare <
        ((8 * (profile.lowerNeighborProduct .plus - 1) : ℕ) : ℚ) ∨
      profile.failureSquare ^ 2 <
        ((64 * (profile.lowerNeighborProduct .minus *
          profile.lowerNeighborProduct .plus) : ℕ) : ℚ))

@[simp] theorem check_eq_true_iff (profile : RankinNeighborProfile) :
    profile.check = true ↔ profile.Valid := by
  simp [check, Valid, and_assoc]

@[simp] theorem closesCutoffCheck_eq_true_iff
    (profile : RankinNeighborProfile) (cutoff : ℕ) :
    profile.closesCutoffCheck cutoff = true ↔
      profile.ClosesCutoff cutoff := by
  simp [closesCutoffCheck, ClosesCutoff, failureSquare]

@[simp] theorem excludesFailureCheck_eq_true_iff
    (profile : RankinNeighborProfile) :
    profile.excludesFailureCheck = true ↔
      profile.ExcludesFailure := by
  simp [excludesFailureCheck, ExcludesFailure]

end RankinNeighborProfile

end BGS.NumberTheory
