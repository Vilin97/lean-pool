/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Assembly.ExactOrderRankinEnvelope

/-!
# A width-sensitive exact-order Rankin envelope

The first exact-order Rankin endpoint bounded the middle-game maximal orders
by all divisors of `p - 1` and `p + 1`.  This file separates that coarse
choice from the analytic argument.  Any certified upper bound for the actual
maximal-order set can now be cubed directly, while the Euler product remains
the same side-erased Rankin product.

This is the interface needed for a joint-antichain or symmetric-chain width
certificate.  It does not assume such a certificate.
-/

namespace BGS.Markoff

open BGS.NumberTheory

/-- The Corvaja--Zannier witness cap obtained from an arbitrary certified
upper bound for the number of maximal candidate orders. -/
def rankinWidthWitnessCap (width : Nat) : Nat :=
  189 * width ^ 3

/-- The side-erased Rankin failure square using a maximal-order width rather
than the total number of neighboring divisors. -/
def rankinWidthJointFailureSquare
    (width rootCap : Nat) (profile : RankinNeighborProfile) : Rat :=
  ((rankinWidthWitnessCap width : Rat) * rootCap *
    (2 * profile.jointCoarseEulerProductProduct)) ^ 2

/-- The chosen integral root cap is sufficient for the width witness. -/
def RankinWidthRootValid (width rootCap : Nat) : Prop :=
  rankinWidthWitnessCap width <= rootCap ^ 12

/-- A direct cutoff leaf for the width-sensitive envelope. -/
def RankinWidthClosesCutoff
    (width rootCap : Nat) (profile : RankinNeighborProfile)
    (cutoff : Nat) : Prop :=
  rankinWidthJointFailureSquare width rootCap profile <
    (8 * (cutoff + 1) : Nat)

/-- A side-erased lower-product contradiction for the width-sensitive
envelope. -/
def RankinWidthExcludesFailure
    (width rootCap : Nat) (profile : RankinNeighborProfile) : Prop :=
  rankinWidthJointFailureSquare width rootCap profile ^ 2 <
    (64 * profile.jointLowerNeighborProduct : Nat)

def rankinWidthLeafCheck
    (width rootCap cutoff : Nat) (profile : RankinNeighborProfile) : Bool :=
  decide
    (rankinWidthWitnessCap width <= rootCap ^ 12 /\
      (rankinWidthJointFailureSquare width rootCap profile <
          ((8 * (cutoff + 1) : Nat) : Rat) \/
        rankinWidthJointFailureSquare width rootCap profile ^ 2 <
          ((64 * profile.jointLowerNeighborProduct : Nat) : Rat)))

@[simp] theorem rankinWidthLeafCheck_eq_true_iff
    (width rootCap cutoff : Nat) (profile : RankinNeighborProfile) :
    rankinWidthLeafCheck width rootCap cutoff profile = true <->
      RankinWidthRootValid width rootCap /\
        (RankinWidthClosesCutoff width rootCap profile cutoff \/
          RankinWidthExcludesFailure width rootCap profile) := by
  simp [rankinWidthLeafCheck, RankinWidthRootValid,
    RankinWidthClosesCutoff, RankinWidthExcludesFailure]

theorem bound_le_rankinWidthWitnessCap
    {p bound width : Nat}
    (hbound :
      bound <= 189 * (middleGameMaximalOrders p bound).card ^ 3)
    (hwidth : (middleGameMaximalOrders p bound).card <= width) :
    bound <= rankinWidthWitnessCap width := by
  exact hbound.trans (by
    simp only [rankinWidthWitnessCap]
    gcongr)

/-- A matched profile and any certified maximal-order width force the new
side-erased failure square.  No divisor-count upper bound occurs here. -/
theorem eight_mul_prime_cast_le_matching_profile_rankinWidthFailureSquare
    {p bound width rootCap : Nat}
    (hpPrime : p.Prime) (hpTwo : 2 < p)
    (hroot :
      8 * p <= (combinedTruncatedOrderTotientSum p bound) ^ 2)
    (hboundWitness :
      bound <= 189 * (middleGameMaximalOrders p bound).card ^ 3)
    (hwidth : (middleGameMaximalOrders p bound).card <= width)
    (profile : RankinNeighborProfile)
    (hprofile : profile.Valid)
    (hmatch : profile.Matches p)
    (hrootValid : RankinWidthRootValid width rootCap) :
    (8 * p : Rat) <=
      rankinWidthJointFailureSquare width rootCap profile := by
  have hp : 1 < p := by omega
  obtain ⟨assignment, hweightNonneg, hweightPower,
      hminusEuler, hplusEuler⟩ :=
    profile.exists_assignedPrimeWeight_bounds
      hpPrime hpTwo hprofile hmatch
  have hboundWidth : bound <= rankinWidthWitnessCap width :=
    bound_le_rankinWidthWitnessCap hboundWitness hwidth
  have hrootCapNonneg : (0 : Rat) <= rootCap := by positivity
  have hrootValidCast :
      (rankinWidthWitnessCap width : Rat) <= (rootCap : Rat) ^ 12 := by
    exact_mod_cast hrootValid
  have hfailure :=
    eight_mul_prime_cast_le_jointRankinSquare
      hp hroot hboundWidth
      (assignedPrimeWeight p profile assignment) rootCap
      hweightNonneg hweightPower hrootCapNonneg hrootValidCast
  have hEuler :
      jointRankinEulerProduct p
          (assignedPrimeWeight p profile assignment) <=
        profile.jointCoarseEulerProduct := by
    change
      ((p - 1).factorization.prod fun prime exponent =>
          rankinPrimePowerFactor prime exponent
            (assignedPrimeWeight p profile assignment prime)) +
        ((p + 1).factorization.prod fun prime exponent =>
          rankinPrimePowerFactor prime exponent
            (assignedPrimeWeight p profile assignment prime)) <=
        profile.coarseEulerProduct .minus +
          profile.coarseEulerProduct .plus
    exact add_le_add hminusEuler hplusEuler
  have hEulerErased :
      jointRankinEulerProduct p
          (assignedPrimeWeight p profile assignment) <=
        2 * profile.jointCoarseEulerProductProduct :=
    hEuler.trans profile.jointCoarseEulerProduct_le_two_mul_product
  have hEulerActualNonneg :=
    jointRankinEulerProduct_nonneg p hp
      (assignedPrimeWeight p profile assignment) hweightNonneg
  have hEulerErasedNonneg :
      (0 : Rat) <= 2 * profile.jointCoarseEulerProductProduct :=
    hEulerActualNonneg.trans hEulerErased
  have hscaleNonneg :
      (0 : Rat) <=
        (rankinWidthWitnessCap width : Rat) * rootCap := by
    positivity
  have hupper :
      (rankinWidthWitnessCap width : Rat) * rootCap *
          jointRankinEulerProduct p
            (assignedPrimeWeight p profile assignment) <=
        (rankinWidthWitnessCap width : Rat) * rootCap *
          (2 * profile.jointCoarseEulerProductProduct) :=
    mul_le_mul_of_nonneg_left hEulerErased hscaleNonneg
  have hleftNonneg :
      (0 : Rat) <=
        (rankinWidthWitnessCap width : Rat) * rootCap *
          jointRankinEulerProduct p
            (assignedPrimeWeight p profile assignment) := by
    positivity
  have hrightNonneg :
      (0 : Rat) <=
        (rankinWidthWitnessCap width : Rat) * rootCap *
          (2 * profile.jointCoarseEulerProductProduct) := by
    exact mul_nonneg hscaleNonneg hEulerErasedNonneg
  simpa only [rankinWidthJointFailureSquare] using
    hfailure.trans ((sq_le_sq₀ hleftNonneg hrightNonneg).2 hupper)

/-- A valid checked width leaf bounds the prime.  This is the replacement
endpoint to be fed by the forthcoming joint-antichain width certificate. -/
theorem prime_le_of_matching_rankinNeighborProfile_rankinWidth_leaf
    {p bound width rootCap cutoff : Nat}
    (hpPrime : p.Prime) (hpTwo : 2 < p)
    (hroot :
      8 * p <= (combinedTruncatedOrderTotientSum p bound) ^ 2)
    (hboundWitness :
      bound <= 189 * (middleGameMaximalOrders p bound).card ^ 3)
    (hwidth : (middleGameMaximalOrders p bound).card <= width)
    (profile : RankinNeighborProfile)
    (hprofile : profile.Valid)
    (hmatch : profile.Matches p)
    (hrootValid : RankinWidthRootValid width rootCap)
    (hleaf :
      RankinWidthClosesCutoff width rootCap profile cutoff \/
        RankinWidthExcludesFailure width rootCap profile) :
    p <= cutoff := by
  have hfailure :=
    eight_mul_prime_cast_le_matching_profile_rankinWidthFailureSquare
      hpPrime hpTwo hroot hboundWitness hwidth profile hprofile hmatch
      hrootValid
  rcases hleaf with hcloses | hexcludes
  · by_contra hnot
    have hcutoffSucc : cutoff + 1 <= p := by omega
    have hcutoffCast :
        (8 * (cutoff + 1) : Rat) <= (8 * p : Rat) := by
      exact_mod_cast Nat.mul_le_mul_left 8 hcutoffSucc
    exact (not_lt_of_ge (hcutoffCast.trans hfailure)) (by
      simpa [RankinWidthClosesCutoff, Nat.cast_mul, Nat.cast_add,
        Nat.cast_ofNat, Nat.cast_one] using hcloses)
  · have hlower := profile.lowerNeighborProducts_le hpPrime hpTwo hmatch
    have hneighborProduct :
        profile.jointLowerNeighborProduct <= (p - 1) * (p + 1) := by
      rw [profile.jointLowerNeighborProduct_eq_mul]
      exact Nat.mul_le_mul hlower.1 hlower.2
    have hneighborLt : (p - 1) * (p + 1) < p ^ 2 := by
      have hsub : p - 1 + 1 = p := by omega
      nlinarith
    have hlowerJointCast :
        ((64 * profile.jointLowerNeighborProduct : Nat) : Rat) <
          (64 * p ^ 2 : Rat) := by
      have hnat := (Nat.mul_lt_mul_left (by omega : 0 < 64)).2
        (hneighborProduct.trans_lt hneighborLt)
      exact_mod_cast hnat
    have hfailureNonneg :
        (0 : Rat) <= rankinWidthJointFailureSquare width rootCap profile := by
      rw [rankinWidthJointFailureSquare]
      exact sq_nonneg _
    have heighthPrimeNonneg : (0 : Rat) <= (8 * p : Rat) := by
      positivity
    have hfailureSquared :
        (64 * p ^ 2 : Rat) <=
          rankinWidthJointFailureSquare width rootCap profile ^ 2 := by
      have hsquare :=
        (sq_le_sq₀ heighthPrimeNonneg hfailureNonneg).2 hfailure
      norm_num [mul_pow] at hsquare ⊢
      exact hsquare
    exact False.elim
      ((not_lt_of_ge (hlowerJointCast.le.trans hfailureSquared)) hexcludes)

end BGS.Markoff
