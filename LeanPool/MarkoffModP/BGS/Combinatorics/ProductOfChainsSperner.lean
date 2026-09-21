/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Combinatorics.SymmetricChainProduct
import LeanPool.MarkoffModP.BGS.NumberTheory.PrimePowerFactorization

/-!
# Sperner bounds for divisor exponent boxes

The divisor lattice attached to prime-power exponents is a product of finite
chains.  The explicit symmetric-chain product construction therefore bounds
every antichain by the central coefficient of
`∏ (1 + X + ... + X^e)`.
-/

namespace BGS.NumberTheory

open BGS.Combinatorics

/-- Exponent vectors, ordered tail-first to match the product constructor. -/
def DivisorExponentBox : List PrimePowerFactor → Type
  | [] => PUnit
  | factor :: factors =>
      DivisorExponentBox factors × Fin (factor.exponent + 1)

instance divisorExponentBoxFintype :
    ∀ factors : List PrimePowerFactor, Fintype (DivisorExponentBox factors)
  | [] => by
      change Fintype PUnit
      infer_instance
  | _ :: factors => by
      letI := divisorExponentBoxFintype factors
      unfold DivisorExponentBox
      infer_instance

instance divisorExponentBoxPartialOrder :
    ∀ factors : List PrimePowerFactor,
      PartialOrder (DivisorExponentBox factors)
  | [] => by
      change PartialOrder PUnit
      infer_instance
  | _ :: factors => by
      letI := divisorExponentBoxPartialOrder factors
      unfold DivisorExponentBox
      infer_instance

/-- Sum of the chosen prime-power exponents. -/
def divisorExponentRank :
    ∀ factors : List PrimePowerFactor, DivisorExponentBox factors → ℕ
  | [], _ => 0
  | _ :: factors, exponentVector =>
      divisorExponentRank factors exponentVector.1 + exponentVector.2

/-- Top rank in the tail-first recursion used by the decomposition. -/
def divisorExponentTotal : List PrimePowerFactor → ℕ
  | [] => 0
  | factor :: factors =>
      divisorExponentTotal factors + factor.exponent

theorem divisorExponentTotal_eq_primePowerTotalExponent
    (factors : List PrimePowerFactor) :
    divisorExponentTotal factors = primePowerTotalExponent factors := by
  induction factors with
  | nil => rfl
  | cons factor factors ih =>
      simp only [divisorExponentTotal, primePowerTotalExponent, ih]
      omega

/-- Explicit symmetric-chain decomposition of every divisor exponent box. -/
def divisorExponentBoxDecomposition :
    ∀ factors : List PrimePowerFactor,
      SymmetricChainDecomposition
        (DivisorExponentBox factors)
        (divisorExponentRank factors)
        (divisorExponentTotal factors)
  | [] => by
      change SymmetricChainDecomposition PUnit (fun _ ↦ 0) 0
      exact SymmetricChainDecomposition.punit
  | factor :: factors => by
      letI := divisorExponentBoxPartialOrder factors
      exact
        (divisorExponentBoxDecomposition factors).productWithChain
          factor.exponent

end BGS.NumberTheory
