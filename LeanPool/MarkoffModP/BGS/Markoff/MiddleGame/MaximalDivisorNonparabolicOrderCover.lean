/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.MaximalDivisorOrderCover

/-!
# Nonparabolic witnesses in maximal right-order subgroups

The maximal-divisor cover already represents every bounded nonparabolic trace
inside a divisibility-maximal right subgroup.  This module records the extra
fact needed for inversion pairing: the representing eigenvalue is not fixed
by inversion.
-/

@[expose] public section

namespace BGS.Markoff

/-- A square-one eigenvalue has parabolic split trace. -/
theorem splitTorusTrace_sq_eq_four_of_sq_eq_one
    {K : Type*} [Field K] (h : Kˣ) (hsq : h ^ 2 = 1) :
    (splitTorusTrace h) ^ 2 = 4 := by
  have hinv : h = h⁻¹ := by
    apply (mul_eq_one_iff_eq_inv.mp)
    simpa only [pow_two] using hsq
  have hinvValue : ((h⁻¹ : Kˣ) : K) = (h : K) := by
    exact congrArg (fun u : Kˣ ↦ (u : K)) hinv.symm
  have hsqValue : (h : K) ^ 2 = 1 := by
    exact congrArg (fun u : Kˣ ↦ (u : K)) hsq
  unfold splitTorusTrace
  rw [hinvValue]
  calc
    ((h : K) + (h : K)) ^ 2 = 4 * (h : K) ^ 2 := by ring
    _ = 4 := by rw [hsqValue, mul_one]

/-- Every bounded nonparabolic trace is represented in a maximal candidate
right subgroup by a non-two-torsion eigenvalue. -/
theorem exists_middleGameMaximalOrder_nonparabolic_trace
    (p currentOrder : ℕ) [Fact p.Prime]
    (hpTwo : p ≠ 2) (hp : 1 < p)
    (t : ZMod p) (hnonparabolic : t ^ 2 ≠ 4)
    (hsmall : rotationOrder t ≤ currentOrder) :
    ∃ m ∈ middleGameMaximalOrders p currentOrder,
      ∃ h₂ : middleGameRightSubgroup p m,
        algebraMap (ZMod p) (quadraticFiniteField p) t =
            splitTorusTrace h₂ ∧
          (((h₂ : (quadraticFiniteField p)ˣ) ^ 2) ≠ 1) := by
  obtain ⟨m, hm, h₂, htrace⟩ :=
    exists_middleGameMaximalOrder_trace_of_nonparabolic
      p currentOrder hpTwo hp t hnonparabolic hsmall
  refine ⟨m, hm, h₂, htrace, ?_⟩
  intro hsq
  apply hnonparabolic
  apply (algebraMap (ZMod p) (quadraticFiniteField p)).injective
  have htraceSq :
      (splitTorusTrace (h₂ : (quadraticFiniteField p)ˣ)) ^ 2 = 4 :=
    splitTorusTrace_sq_eq_four_of_sq_eq_one
      (h₂ : (quadraticFiniteField p)ˣ) hsq
  simpa only [map_pow, map_ofNat, htrace] using htraceSq

end BGS.Markoff
