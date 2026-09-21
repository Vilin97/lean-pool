/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Endgame.PrimitiveInclusionExclusion
import LeanPool.MarkoffModP.BGS.Markoff.Endgame.PowerCoverCounting

/-!
# One-sided primitive extraction with witness multiplicities

The cage fiber-product count has an arbitrary finite witness type on the left
and a cyclic multiplicative group on the right.  This file performs Möbius
inversion without erasing the left witness.
-/

namespace BGS

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

variable {A H T : Type*} [CommGroup H]

/-- Witness/parameter pairs satisfying a relation. -/
noncomputable def rightTraceRelationPairs
    [Finite A] [Finite H] (leftTrace : A → T) (rightTrace : H → T) :
    Finset (A × H) := by
  classical
  letI := Fintype.ofFinite A
  letI := Fintype.ofFinite H
  exact Finset.univ.filter fun z => leftTrace z.1 = rightTrace z.2

/-- Relation pairs whose right parameter has exact multiplicative order. -/
noncomputable def rightTraceExactOrderSolutions
    [Finite A] [Finite H] (leftTrace : A → T) (rightTrace : H → T)
    (order : ℕ) : Finset (A × H) := by
  classical
  exact (rightTraceRelationPairs leftTrace rightTrace).filter fun z =>
    orderOf z.2 = order

/-- Relation pairs whose right parameter is killed by a specified power. -/
noncomputable def rightTracePowerKernelSolutions
    [Finite A] [Finite H] (leftTrace : A → T) (rightTrace : H → T)
    (exponent : ℕ) : Finset (A × H) := by
  classical
  exact (rightTraceRelationPairs leftTrace rightTrace).filter fun z =>
    z.2 ^ exponent = 1

/-- Relation pairs with the right parameter restricted to a power-map image. -/
def rightPowerTraceRangeSolutions
    (leftTrace : A → T) (rightTrace : H → T) (exponent : ℕ) :=
  {z : A × (powMonoidHom exponent : H →* H).range //
    leftTrace z.1 = rightTrace z.2}

/-- The one-sided power cover before quotienting by the power-map fibers. -/
def rightPowerTraceCoverSolutions
    (leftTrace : A → T) (rightTrace : H → T) (exponent : ℕ) :=
  {z : A × H // leftTrace z.1 = rightTrace (z.2 ^ exponent)}

/-- A one-sided cover point is a range solution together with a point in the
corresponding power-map fiber. -/
def rightPowerTraceCoverEquivSigmaFiber
    (leftTrace : A → T) (rightTrace : H → T) (exponent : ℕ) :
    rightPowerTraceCoverSolutions leftTrace rightTrace exponent ≃
      Σ s : rightPowerTraceRangeSolutions leftTrace rightTrace exponent,
        ((powMonoidHom exponent : H →* H) ⁻¹' {(s.1.2 : H)} : Set H) where
  toFun z :=
    ⟨⟨(z.1.1, ⟨z.1.2 ^ exponent, ⟨z.1.2, by simp⟩⟩), z.2⟩,
      ⟨z.1.2, by simp⟩⟩
  invFun z := ⟨(z.1.1.1, z.2.1), by
    have hz : (powMonoidHom exponent : H →* H) z.2.1 = (z.1.1.2 : H) := z.2.2
    change leftTrace z.1.1.1 = rightTrace (z.2.1 ^ exponent)
    rw [show z.2.1 ^ exponent = z.1.1.2 by exact hz]
    exact z.1.2⟩
  left_inv z := by rfl
  right_inv z := by
    rcases z with ⟨⟨⟨a, ⟨u, huRange⟩⟩, htrace⟩, ⟨root, hroot⟩⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hroot
    dsimp at hroot ⊢
    subst u
    rfl

/-- Exact one-sided power-cover multiplicity. -/
theorem natCard_rightPowerTraceCoverSolutions
    [Finite A] [Finite H]
    (leftTrace : A → T) (rightTrace : H → T) (exponent : ℕ) :
    Nat.card (rightPowerTraceCoverSolutions leftTrace rightTrace exponent) =
      Nat.card (powMonoidHom exponent : H →* H).ker *
        Nat.card (rightPowerTraceRangeSolutions leftTrace rightTrace exponent) := by
  letI : Finite (powMonoidHom exponent : H →* H).range :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite (rightPowerTraceRangeSolutions leftTrace rightTrace exponent) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI := Fintype.ofFinite
    (rightPowerTraceRangeSolutions leftTrace rightTrace exponent)
  rw [Nat.card_congr
    (rightPowerTraceCoverEquivSigmaFiber leftTrace rightTrace exponent),
    Nat.card_sigma]
  simp_rw [BGS.Markoff.natCard_powerMapFiber_eq_ker]
  simp [Nat.mul_comm]

/-- For a divisor exponent in a finite cyclic group, the one-sided cover has
exactly `d` points above every power-range solution. -/
theorem natCard_rightPowerTraceCoverSolutions_of_dvd
    [Finite A] [Finite H] [IsCyclic H]
    (leftTrace : A → T) (rightTrace : H → T) (d : ℕ)
    (hd : d ∣ Nat.card H) :
    Nat.card (rightPowerTraceCoverSolutions leftTrace rightTrace d) =
      d * Nat.card (rightPowerTraceRangeSolutions leftTrace rightTrace d) := by
  rw [natCard_rightPowerTraceCoverSolutions,
    IsCyclic.card_powMonoidHom_ker,
    Nat.gcd_eq_right_iff_dvd.mpr hd]

@[simp]
theorem mem_rightTraceExactOrderSolutions_iff
    [Finite A] [Finite H] (leftTrace : A → T) (rightTrace : H → T)
    (order : ℕ) (z : A × H) :
    z ∈ rightTraceExactOrderSolutions leftTrace rightTrace order ↔
      leftTrace z.1 = rightTrace z.2 ∧ orderOf z.2 = order := by
  classical
  simp [rightTraceExactOrderSolutions, rightTraceRelationPairs]

@[simp]
theorem mem_rightTracePowerKernelSolutions_iff
    [Finite A] [Finite H] (leftTrace : A → T) (rightTrace : H → T)
    (exponent : ℕ) (z : A × H) :
    z ∈ rightTracePowerKernelSolutions leftTrace rightTrace exponent ↔
      leftTrace z.1 = rightTrace z.2 ∧ z.2 ^ exponent = 1 := by
  classical
  simp [rightTracePowerKernelSolutions, rightTraceRelationPairs]

/-- Exact-order classes partition the relation pairs killed by one power. -/
theorem sum_rightTraceExactOrderSolutions_card_eq_powerKernel_card
    [Finite A] [Finite H] (leftTrace : A → T) (rightTrace : H → T)
    (m : ℕ) (hm : 0 < m) :
    ∑ order ∈ m.divisors,
        (rightTraceExactOrderSolutions leftTrace rightTrace order).card =
      (rightTracePowerKernelSolutions leftTrace rightTrace m).card := by
  classical
  simp only [rightTraceExactOrderSolutions]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  apply congrArg Finset.card
  ext z
  simp [rightTracePowerKernelSolutions, Nat.mem_divisors, hm.ne',
    orderOf_dvd_iff_pow_eq_one]

/-- Möbius inversion recovers the witness-bearing exact-order count. -/
theorem moebius_sum_rightTracePowerKernel_card_eq_exactOrder_card
    [Finite A] [Finite H] (leftTrace : A → T) (rightTrace : H → T)
    (n : ℕ) (hn : 0 < n) :
    ∑ x ∈ n.divisorsAntidiagonal,
        (μ x.fst : ℤ) *
          (rightTracePowerKernelSolutions leftTrace rightTrace x.snd).card =
      (rightTraceExactOrderSolutions leftTrace rightTrace n).card := by
  have hinversion :=
    (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (R := ℤ)
      (f := fun order =>
        ((rightTraceExactOrderSolutions leftTrace rightTrace order).card : ℤ))
      (g := fun exponent =>
        ((rightTracePowerKernelSolutions leftTrace rightTrace exponent).card : ℤ))).mp
      (fun m hm => by
        exact_mod_cast
          sum_rightTraceExactOrderSolutions_card_eq_powerKernel_card
            leftTrace rightTrace m hm)
  exact hinversion n hn

/-- A right power-range witness is a right power-kernel witness when the
corresponding subgroups agree. -/
def rightPowerTraceRangeSolutionsEquivPowerKernelSolutions
    [Finite A] [Finite H]
    (leftTrace : A → T) (rightTrace : H → T)
    (rangeExponent kernelExponent : ℕ)
    (hsubgroup :
      (powMonoidHom rangeExponent : H →* H).range =
        (powMonoidHom kernelExponent : H →* H).ker) :
    rightPowerTraceRangeSolutions leftTrace rightTrace rangeExponent ≃
      ↥(rightTracePowerKernelSolutions leftTrace rightTrace kernelExponent) where
  toFun z := ⟨(z.1.1, z.1.2.1), by
    rw [mem_rightTracePowerKernelSolutions_iff]
    refine ⟨z.2, ?_⟩
    have hzker : z.1.2.1 ∈ (powMonoidHom kernelExponent : H →* H).ker := by
      rw [← hsubgroup]
      exact z.1.2.2
    exact hzker⟩
  invFun z := ⟨(z.1.1, ⟨z.1.2, by
    rw [hsubgroup]
    exact (mem_rightTracePowerKernelSolutions_iff
      leftTrace rightTrace kernelExponent z.1).mp z.2 |>.2⟩),
    (mem_rightTracePowerKernelSolutions_iff
      leftTrace rightTrace kernelExponent z.1).mp z.2 |>.1⟩
  left_inv z := by rfl
  right_inv z := by rfl

theorem natCard_rightPowerTraceRangeSolutions_eq_powerKernel_card
    [Finite A] [Finite H]
    (leftTrace : A → T) (rightTrace : H → T)
    (rangeExponent kernelExponent : ℕ)
    (hsubgroup :
      (powMonoidHom rangeExponent : H →* H).range =
        (powMonoidHom kernelExponent : H →* H).ker) :
    Nat.card (rightPowerTraceRangeSolutions leftTrace rightTrace rangeExponent) =
      (rightTracePowerKernelSolutions leftTrace rightTrace kernelExponent).card := by
  calc
    Nat.card (rightPowerTraceRangeSolutions leftTrace rightTrace rangeExponent) =
        Nat.card ↥(rightTracePowerKernelSolutions
          leftTrace rightTrace kernelExponent) :=
      Nat.card_congr
        (rightPowerTraceRangeSolutionsEquivPowerKernelSolutions
          leftTrace rightTrace rangeExponent kernelExponent hsubgroup)
    _ = (rightTracePowerKernelSolutions
        leftTrace rightTrace kernelExponent).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]

/-- Published one-sided inclusion--exclusion, retaining every left witness. -/
theorem moebius_sum_rightPowerTraceRange_card_eq_exactOrder_card
    [Finite A] [Finite H] [IsCyclic H]
    (leftTrace : A → T) (rightTrace : H → T) :
    ∑ x ∈ (Nat.card H).divisorsAntidiagonal,
        (μ x.fst : ℤ) *
          Nat.card (rightPowerTraceRangeSolutions
            leftTrace rightTrace x.fst) =
      (rightTraceExactOrderSolutions
        leftTrace rightTrace (Nat.card H)).card := by
  rw [← moebius_sum_rightTracePowerKernel_card_eq_exactOrder_card
    leftTrace rightTrace (Nat.card H) Nat.card_pos]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  have hproduct := (Nat.mem_divisorsAntidiagonal.mp hx).1
  have hleftNe : x.fst ≠ 0 := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx
  have hdvd : x.fst ∣ Nat.card H := ⟨x.snd, hproduct.symm⟩
  have hquotient : Nat.card H / x.fst = x.snd := by
    rw [← hproduct, Nat.mul_comm x.fst x.snd,
      Nat.mul_div_left x.snd (Nat.pos_of_ne_zero hleftNe)]
  rw [natCard_rightPowerTraceRangeSolutions_eq_powerKernel_card
    leftTrace rightTrace x.fst x.snd]
  simpa [hquotient] using
    BGS.Markoff.powMonoidHom_range_eq_ker_complementaryExponent
      (H := H) x.fst hdvd

/-- Pointwise range-count estimates give the divisor-count error envelope for
the witness-bearing primitive count. -/
theorem rightTraceExactOrderSolutions_card_error_le_moebiusMain
    [Finite A] [Finite H] [IsCyclic H]
    (leftTrace : A → T) (rightTrace : H → T)
    (mainTerm : ℕ → ℝ) (error : ℝ)
    (hRange : ∀ d : ℕ, d ∣ Nat.card H → 0 < d →
      |(Nat.card (rightPowerTraceRangeSolutions
          leftTrace rightTrace d) : ℝ) - mainTerm d| ≤ error) :
    |((rightTraceExactOrderSolutions
        leftTrace rightTrace (Nat.card H)).card : ℝ) -
        ∑ x ∈ (Nat.card H).divisorsAntidiagonal,
          (μ x.fst : ℝ) * mainTerm x.fst| ≤
      ((Nat.card H).divisors.card : ℝ) * error := by
  have hExact :=
    moebius_sum_rightPowerTraceRange_card_eq_exactOrder_card
      leftTrace rightTrace
  have hExactReal :
      ((rightTraceExactOrderSolutions
        leftTrace rightTrace (Nat.card H)).card : ℝ) =
        ∑ x ∈ (Nat.card H).divisorsAntidiagonal,
          (μ x.fst : ℝ) *
            (Nat.card (rightPowerTraceRangeSolutions
              leftTrace rightTrace x.fst) : ℝ) := by
    exact_mod_cast hExact.symm
  rw [hExactReal]
  apply BGS.Markoff.abs_moebius_weighted_sum_sub_le_divisors_card_mul
    (Nat.card H)
    (fun x => (Nat.card (rightPowerTraceRangeSolutions
      leftTrace rightTrace x.fst) : ℝ))
    (fun x => mainTerm x.fst) error
  intro x hx
  have hproduct := (Nat.mem_divisorsAntidiagonal.mp hx).1
  have hdvd : x.fst ∣ Nat.card H := ⟨x.snd, hproduct.symm⟩
  exact hRange x.fst hdvd
    (Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx))

/-- If the Möbius main term dominates the divisor error, a primitive right
parameter exists together with a genuine left witness. -/
theorem rightTraceExactOrderSolutions_nonempty_of_divisorsError_lt_moebiusMain
    [Finite A] [Finite H] [IsCyclic H]
    (leftTrace : A → T) (rightTrace : H → T)
    (mainTerm : ℕ → ℝ) (error : ℝ)
    (hRange : ∀ d : ℕ, d ∣ Nat.card H → 0 < d →
      |(Nat.card (rightPowerTraceRangeSolutions
          leftTrace rightTrace d) : ℝ) - mainTerm d| ≤ error)
    (hpositive :
      ((Nat.card H).divisors.card : ℝ) * error <
        ∑ x ∈ (Nat.card H).divisorsAntidiagonal,
          (μ x.fst : ℝ) * mainTerm x.fst) :
    (rightTraceExactOrderSolutions
      leftTrace rightTrace (Nat.card H)).Nonempty := by
  have henvelope := rightTraceExactOrderSolutions_card_error_le_moebiusMain
    leftTrace rightTrace mainTerm error hRange
  have hcardReal :
      0 < ((rightTraceExactOrderSolutions
        leftTrace rightTrace (Nat.card H)).card : ℝ) := by
    have hlower :
        (∑ x ∈ (Nat.card H).divisorsAntidiagonal,
          (μ x.fst : ℝ) * mainTerm x.fst) -
            ((rightTraceExactOrderSolutions
              leftTrace rightTrace (Nat.card H)).card : ℝ) ≤
          |((rightTraceExactOrderSolutions
              leftTrace rightTrace (Nat.card H)).card : ℝ) -
            ∑ x ∈ (Nat.card H).divisorsAntidiagonal,
              (μ x.fst : ℝ) * mainTerm x.fst| := by
      simpa only [neg_sub] using
        neg_le_abs
          (((rightTraceExactOrderSolutions
            leftTrace rightTrace (Nat.card H)).card : ℝ) -
              ∑ x ∈ (Nat.card H).divisorsAntidiagonal,
                (μ x.fst : ℝ) * mainTerm x.fst)
    linarith
  exact Finset.card_pos.mp (by exact_mod_cast hcardReal)

end

end BGS
