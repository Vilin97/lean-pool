/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.GKPCarry.InfiniteSieve
import Mathlib.Data.Nat.Cast.Order.Field

/-!
# A density-one theorem for the GKP power-of-two condition

The exact modular sieve bounds possible failures in every initial interval.
At ternary depth `n + 3`, each block of `2 * 3 ^ (n + 2)` exponents contains
at most `(n + 9) * 2 ^ n` failures.  These bounds prove that the proportion of
exponents `k` for which `9` does not divide `centralBinom (2 ^ k)` tends to
zero.  Thus the GKP divisibility conclusion holds for a set of exponents of
natural density one.

The universal conjecture remains open because a density-zero failure set need
not be empty.
-/

namespace GKPCarry

/-- Possible GKP failures among exponents below `bound`. -/
abbrev GKPFailureExponentsBelow (bound : ℕ) :=
  {exponent : Fin bound //
    ¬ 9 ∣ Nat.centralBinom (2 ^ exponent.val)}

/-- Exponents below `bound` that satisfy the GKP divisibility condition. -/
abbrev GKPSuccessExponentsBelow (bound : ℕ) :=
  {exponent : Fin bound //
    9 ∣ Nat.centralBinom (2 ^ exponent.val)}

/-- Encode a possible failure by its quotient block and its uncertified
residue class at a chosen ternary depth. -/
private def gkpFailureBlockEmbedding (depth bound : ℕ) :
    GKPFailureExponentsBelow bound ↪
      Fin (bound / (2 * 3 ^ (depth + 2)) + 1) ×
        UncertifiedExponentClasses depth where
  toFun exponent := by
    let residue : Fin (2 * 3 ^ (depth + 2)) :=
      ⟨exponent.val.val % (2 * 3 ^ (depth + 2)),
        Nat.mod_lt _ (by positivity)⟩
    have huncertified :
        ternaryDoubleCarryCount
          (Nat.digits 3 (2 ^ residue.val % 3 ^ (depth + 3))) < 2 := by
      by_contra hcarry
      have htwoResidue :
          2 ≤ ternaryDoubleCarryCount
            (Nat.digits 3 (2 ^ residue.val % 3 ^ (depth + 3))) := by
        omega
      have htwo :
          2 ≤ ternaryDoubleCarryCount
            (Nat.digits 3
              (2 ^ (exponent.val.val % (2 * 3 ^ (depth + 2))) %
                3 ^ (depth + 3))) := by
        simpa only [residue] using htwoResidue
      exact exponent.property
        (nine_dvd_centralBinom_two_pow_of_reduced_carry_certificate
          depth exponent.val.val htwo)
    exact
      (⟨exponent.val.val / (2 * 3 ^ (depth + 2)),
          Nat.lt_succ_of_le
            (Nat.div_le_div_right (Nat.le_of_lt exponent.val.isLt))⟩,
        ⟨residue, huncertified⟩)
  inj' := by
    intro exponent₁ exponent₂ hequal
    apply Subtype.ext
    apply Fin.ext
    have hquotient := congrArg (fun pair => pair.1.val) hequal
    have hremainder := congrArg (fun pair => pair.2.val.val) hequal
    change
      exponent₁.val.val / (2 * 3 ^ (depth + 2)) =
        exponent₂.val.val / (2 * 3 ^ (depth + 2)) at hquotient
    change
      exponent₁.val.val % (2 * 3 ^ (depth + 2)) =
        exponent₂.val.val % (2 * 3 ^ (depth + 2)) at hremainder
    calc
      exponent₁.val.val =
          exponent₁.val.val % (2 * 3 ^ (depth + 2)) +
            (2 * 3 ^ (depth + 2)) *
              (exponent₁.val.val / (2 * 3 ^ (depth + 2))) :=
        (Nat.mod_add_div _ _).symm
      _ = exponent₂.val.val % (2 * 3 ^ (depth + 2)) +
            (2 * 3 ^ (depth + 2)) *
              (exponent₂.val.val / (2 * 3 ^ (depth + 2))) := by
        rw [hremainder, hquotient]
      _ = exponent₂.val.val := Nat.mod_add_div _ _

/-- Quantitative sieve bound in every initial interval. -/
theorem card_gkpFailureExponentsBelow_le (depth bound : ℕ) :
    Fintype.card (GKPFailureExponentsBelow bound) ≤
      (bound / (2 * 3 ^ (depth + 2)) + 1) *
        ((depth + 9) * 2 ^ depth) := by
  calc
    Fintype.card (GKPFailureExponentsBelow bound) ≤
        Fintype.card
          (Fin (bound / (2 * 3 ^ (depth + 2)) + 1) ×
            UncertifiedExponentClasses depth) :=
      Fintype.card_le_of_injective
        (gkpFailureBlockEmbedding depth bound)
        (gkpFailureBlockEmbedding depth bound).injective
    _ = (bound / (2 * 3 ^ (depth + 2)) + 1) *
          ((depth + 9) * 2 ^ depth) := by
      rw [Fintype.card_prod, Fintype.card_fin,
        card_uncertifiedExponentClasses]

/-- Proportion of possible GKP failures among exponents below `bound`. -/
noncomputable def gkpFailureProportion (bound : ℕ) : ℝ :=
  Fintype.card (GKPFailureExponentsBelow bound) / bound

/-- At any fixed sieve depth, the failure proportion is bounded by the
residual periodic proportion plus one incomplete block. -/
theorem gkpFailureProportion_le (depth bound : ℕ) (hbound : 0 < bound) :
    gkpFailureProportion bound ≤
      uncertifiedClassProportion depth +
        (((depth + 9) * 2 ^ depth : ℕ) : ℝ) / bound := by
  have hcard := card_gkpFailureExponentsBelow_le depth bound
  have hcardReal :
      (Fintype.card (GKPFailureExponentsBelow bound) : ℝ) ≤
        (((bound / (2 * 3 ^ (depth + 2)) + 1) *
          ((depth + 9) * 2 ^ depth) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hboundReal : (0 : ℝ) < bound := by exact_mod_cast hbound
  have hperiodReal : (0 : ℝ) < (2 * 3 ^ (depth + 2) : ℕ) := by
    positivity
  have hratio :
      uncertifiedClassProportion depth =
        (((depth + 9) * 2 ^ depth : ℕ) : ℝ) /
          (2 * 3 ^ (depth + 2) : ℕ) := by
    rw [uncertifiedClassProportion_eq_card_ratio,
      card_uncertifiedExponentClasses, Fintype.card_fin]
  unfold gkpFailureProportion
  calc
    (Fintype.card (GKPFailureExponentsBelow bound) : ℝ) / bound ≤
        (((bound / (2 * 3 ^ (depth + 2)) + 1) *
          ((depth + 9) * 2 ^ depth) : ℕ) : ℝ) / bound :=
      (div_le_div_iff_of_pos_right hboundReal).2 hcardReal
    _ = (((bound / (2 * 3 ^ (depth + 2)) : ℕ) : ℝ) + 1) *
          (((depth + 9) * 2 ^ depth : ℕ) : ℝ) / bound := by
      norm_num
    _ ≤ (((bound : ℝ) / (2 * 3 ^ (depth + 2) : ℕ)) + 1) *
          (((depth + 9) * 2 ^ depth : ℕ) : ℝ) / bound := by
      gcongr
      exact Nat.cast_div_le
    _ = (((depth + 9) * 2 ^ depth : ℕ) : ℝ) /
          (2 * 3 ^ (depth + 2) : ℕ) +
        (((depth + 9) * 2 ^ depth : ℕ) : ℝ) / bound := by
      field_simp
    _ = uncertifiedClassProportion depth +
        (((depth + 9) * 2 ^ depth : ℕ) : ℝ) / bound := by
      rw [hratio]

/-- **Density-zero failure theorem.** The proportion of exponents below
`bound` that fail the GKP divisibility condition tends to zero. -/
theorem tendsto_gkpFailureProportion_zero :
    Filter.Tendsto gkpFailureProportion Filter.atTop (nhds 0) := by
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨depth, hdepth⟩ :=
    Metric.tendsto_atTop.mp tendsto_uncertifiedClassProportion
      (ε / 2) hhalf
  have hresidualNonnegative :
      0 ≤ uncertifiedClassProportion depth := by
    rw [uncertifiedClassProportion_eq_card_ratio]
    positivity
  have hresidual : uncertifiedClassProportion depth < ε / 2 := by
    have := hdepth depth le_rfl
    simpa [Real.dist_eq, abs_of_nonneg hresidualNonnegative] using this
  let blockError : ℝ := (((depth + 9) * 2 ^ depth : ℕ) : ℝ)
  have hblockErrorLimit :
      Filter.Tendsto (fun bound : ℕ => blockError / bound)
        Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat blockError
  obtain ⟨threshold, hthreshold⟩ :=
    Metric.tendsto_atTop.mp hblockErrorLimit (ε / 2) hhalf
  refine ⟨max threshold 1, fun bound hbound => ?_⟩
  have hthresholdBound : threshold ≤ bound :=
    (le_max_left threshold 1).trans hbound
  have honeBound : 1 ≤ bound :=
    (le_max_right threshold 1).trans hbound
  have hboundPositive : 0 < bound := Nat.zero_lt_of_lt honeBound
  have hblockErrorNonnegative : 0 ≤ blockError := by
    dsimp only [blockError]
    positivity
  have hblockNonnegative : 0 ≤ blockError / (bound : ℝ) := by
    positivity
  have hblock : blockError / (bound : ℝ) < ε / 2 := by
    have := hthreshold bound hthresholdBound
    simpa [Real.dist_eq, abs_of_nonneg hblockNonnegative,
      abs_of_nonneg hblockErrorNonnegative] using this
  have hfailureNonnegative : 0 ≤ gkpFailureProportion bound := by
    unfold gkpFailureProportion
    positivity
  have hfailureBound :=
    gkpFailureProportion_le depth bound hboundPositive
  change
    gkpFailureProportion bound ≤
      uncertifiedClassProportion depth + blockError / bound at hfailureBound
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hfailureNonnegative]
  exact hfailureBound.trans_lt (by linarith)

/-- Proportion of exponents below `bound` satisfying the divisibility
condition. -/
noncomputable def gkpSuccessProportion (bound : ℕ) : ℝ :=
  Fintype.card (GKPSuccessExponentsBelow bound) / bound

theorem gkpSuccessProportion_eq_one_sub_failure
    (bound : ℕ) (hbound : 0 < bound) :
    gkpSuccessProportion bound = 1 - gkpFailureProportion bound := by
  classical
  let failure := fun exponent : Fin bound =>
    ¬ 9 ∣ Nat.centralBinom (2 ^ exponent.val)
  have hsuccess :
      Fintype.card (GKPSuccessExponentsBelow bound) =
        Fintype.card {exponent : Fin bound // ¬ failure exponent} := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun exponent => by
      simp only [failure, not_not])
  have hfailure :
      Fintype.card (GKPFailureExponentsBelow bound) =
        Fintype.card {exponent : Fin bound // failure exponent} := by
    rfl
  have hpartition :
      Fintype.card (GKPSuccessExponentsBelow bound) +
          Fintype.card (GKPFailureExponentsBelow bound) = bound := by
    rw [hsuccess, hfailure, Fintype.card_subtype_compl, Fintype.card_fin]
    exact Nat.sub_add_cancel (by
      simpa using Fintype.card_subtype_le failure)
  have hpartitionReal :
      (Fintype.card (GKPSuccessExponentsBelow bound) : ℝ) +
          Fintype.card (GKPFailureExponentsBelow bound) = bound := by
    exact_mod_cast hpartition
  unfold gkpSuccessProportion gkpFailureProportion
  have hboundReal : (bound : ℝ) ≠ 0 := by positivity
  field_simp
  linarith

/-- **Density-one GKP theorem.** Powers of two satisfy the divisibility branch
of the GKP conjecture for a set of exponents of natural density one. -/
theorem tendsto_gkpSuccessProportion_one :
    Filter.Tendsto gkpSuccessProportion Filter.atTop (nhds 1) := by
  have hone :
      Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have hcomplement := hone.sub tendsto_gkpFailureProportion_zero
  have hcomplement' :
      Filter.Tendsto (fun bound => 1 - gkpFailureProportion bound)
        Filter.atTop (nhds 1) := by
    convert hcomplement using 1
    norm_num
  refine Filter.Tendsto.congr' ?_ hcomplement'
  filter_upwards [Filter.eventually_ge_atTop 1] with bound hbound
  exact (gkpSuccessProportion_eq_one_sub_failure bound
    (Nat.zero_lt_of_lt hbound)).symm

end GKPCarry
