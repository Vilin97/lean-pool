/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.GKPCarry.InfiniteSlices
import LeanPool.GKPCarry.UnitCarryCounting
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.Card

/-!
# An exact all-depth modular sieve for GKP carries

For every ternary prefix depth `n + 3`, powers of two have exact period
`2 * 3 ^ (n + 2)`.  In one period, precisely `(n + 9) * 2 ^ n` exponent
classes have fewer than two visible doubling carries.  Every other class is
an infinite congruence class on which the central binomial coefficient is
divisible by nine.

This is an exact infinite family of certified cases.  The uncertified classes
at each finite depth may acquire carries later; this theorem neither decides
them nor proves the universal GKP conjecture.
-/

namespace GKPCarry

/-- One exponent period is equivalent to all fixed-length ternary unit words. -/
noncomputable def twoPowerTernaryUnitWordEquiv (length : ℕ) :
    Fin (2 * 3 ^ length) ≃ TernaryUnitWords length :=
  (twoPowerUnitEquiv length).trans (ternaryUnitWordEquiv length).symm

/-- The word corresponding to an exponent is the fixed-length ternary
expansion of its power-of-two residue. -/
theorem ternaryWordValue_twoPowerTernaryUnitWordEquiv_apply
    (length : ℕ) (exponent : Fin (2 * 3 ^ length)) :
    ternaryWordValue (twoPowerTernaryUnitWordEquiv length exponent).val =
      2 ^ exponent.val % 3 ^ (length + 1) := by
  have hunit :
      ternaryUnitWordEquiv length
          (twoPowerTernaryUnitWordEquiv length exponent) =
        twoPowerUnitEquiv length exponent := by
    simp [twoPowerTernaryUnitWordEquiv]
  have hvalue := congrArg
    (fun unit : (ZMod (3 ^ (length + 1)))ˣ =>
      ((unit : ZMod (3 ^ (length + 1))).val)) hunit
  rw [val_ternaryUnitWordEquiv_apply,
    val_twoPowerUnitEquiv_apply] at hvalue
  exact hvalue

/-- Exponent classes not yet certified after reading `n + 3` ternary digits.
They are not counterexamples: later digits may supply the missing carries. -/
abbrev UncertifiedExponentClasses (n : ℕ) :=
  {exponent : Fin (2 * 3 ^ (n + 2)) //
    ternaryDoubleCarryCount
      (Nat.digits 3 (2 ^ exponent.val % 3 ^ (n + 3))) < 2}

/-- Exponent classes certified after reading `n + 3` ternary digits. -/
abbrev CertifiedExponentClasses (n : ℕ) :=
  {exponent : Fin (2 * 3 ^ (n + 2)) //
    2 ≤ ternaryDoubleCarryCount
      (Nat.digits 3 (2 ^ exponent.val % 3 ^ (n + 3)))}

private lemma unitWord_bad_iff_carryCount_lt_two {length : ℕ}
    (word : TernaryUnitWords length) :
    badCarryStateAux (ternaryWordDigits word.val) .zeroCarry ≠ .good ↔
      ternaryDoubleCarryCount (ternaryWordDigits word.val) < 2 := by
  have hvalid :
      ∀ digit ∈ ternaryWordDigits word.val, digit < 3 := by
    simp [ternaryWordDigits]
  simpa [ternaryDoubleCarryCount, BadCarryState.incomingCarry,
    BadCarryState.neededCarries] using
      (badCarryStateAux_ne_good_iff_carryCount_lt_needed
        (ternaryWordDigits word.val) hvalid .zeroCarry)

/-- The uncertified exponent classes are exactly the deficient unit words
counted by the carry automaton. -/
noncomputable def uncertifiedExponentClassesEquivUnitBadCarryWords (n : ℕ) :
    UncertifiedExponentClasses n ≃ UnitBadCarryWords (n + 2) :=
  (twoPowerTernaryUnitWordEquiv (n + 2)).subtypeEquiv (fun exponent => by
    let word := twoPowerTernaryUnitWordEquiv (n + 2) exponent
    have hvalue :
        ternaryWordValue word.val =
          2 ^ exponent.val % 3 ^ (n + 3) := by
      simpa [word, show n + 2 + 1 = n + 3 by omega] using
        (ternaryWordValue_twoPowerTernaryUnitWordEquiv_apply
          (n + 2) exponent)
    have hcount := ternaryDoubleCarryCount_word_eq_value word.val
    rw [← hvalue, ← hcount]
    exact (unitWord_bad_iff_carryCount_lt_two word).symm)

/-- Exact residual count: after `n + 3` digits, precisely
`(n + 9) * 2 ^ n` exponent classes remain uncertified. -/
theorem card_uncertifiedExponentClasses (n : ℕ) :
    Fintype.card (UncertifiedExponentClasses n) =
      (n + 9) * 2 ^ n := by
  rw [Fintype.card_congr
    (uncertifiedExponentClassesEquivUnitBadCarryWords n),
    card_unitBadCarryWords]

/-- The complementary certified set has the corresponding exact size. -/
theorem card_certifiedExponentClasses (n : ℕ) :
    Fintype.card (CertifiedExponentClasses n) =
      2 * 3 ^ (n + 2) - (n + 9) * 2 ^ n := by
  let deficient := fun exponent : Fin (2 * 3 ^ (n + 2)) =>
    ternaryDoubleCarryCount
      (Nat.digits 3 (2 ^ exponent.val % 3 ^ (n + 3))) < 2
  have hdeficient :
      Fintype.card {exponent : Fin (2 * 3 ^ (n + 2)) // deficient exponent} =
        (n + 9) * 2 ^ n := by
    change Fintype.card (UncertifiedExponentClasses n) =
      (n + 9) * 2 ^ n
    exact card_uncertifiedExponentClasses n
  have hcomplement :
      Fintype.card {exponent : Fin (2 * 3 ^ (n + 2)) // ¬ deficient exponent} =
        2 * 3 ^ (n + 2) - (n + 9) * 2 ^ n := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, hdeficient]
  let hcertified :
      CertifiedExponentClasses n ≃
        {exponent : Fin (2 * 3 ^ (n + 2)) // ¬ deficient exponent} :=
    Equiv.subtypeEquivRight (fun exponent => by
      dsimp only [deficient]
      omega)
  rw [Fintype.card_congr hcertified]
  exact hcomplement

/-! ## Asymptotic strength of the sieve -/

/-- The proportion of exponent classes left uncertified at depth `n + 3`,
written in a form that exposes its geometric decay. -/
noncomputable def uncertifiedClassProportion (n : ℕ) : ℝ :=
  ((n : ℝ) + 9) / 18 * ((2 : ℝ) / 3) ^ n

/-- The analytic proportion is exactly the ratio of the residual class count
to the full exponent period. -/
theorem uncertifiedClassProportion_eq_card_ratio (n : ℕ) :
    uncertifiedClassProportion n =
      Fintype.card (UncertifiedExponentClasses n) /
        Fintype.card (Fin (2 * 3 ^ (n + 2))) := by
  rw [card_uncertifiedExponentClasses, Fintype.card_fin]
  simp only [uncertifiedClassProportion, Nat.cast_mul, Nat.cast_add,
    Nat.cast_ofNat, Nat.cast_pow]
  rw [div_pow]
  field_simp
  ring_nf

/-- The proportion of exponent classes left unresolved by the finite-prefix
sieve tends to zero as the prefix depth increases. -/
theorem tendsto_uncertifiedClassProportion :
    Filter.Tendsto uncertifiedClassProportion Filter.atTop (nhds 0) := by
  have hlinear := tendsto_self_mul_const_pow_of_lt_one
    (r := (2 : ℝ) / 3) (by norm_num) (by norm_num)
  have hgeometric :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (𝕜 := ℝ) (r := (2 : ℝ) / 3) (by norm_num) (by norm_num)
  have hsum := hlinear.add (hgeometric.const_mul 9)
  have hscaled := hsum.mul_const ((18 : ℝ)⁻¹)
  convert hscaled using 1
  · funext n
    simp only [uncertifiedClassProportion]
    ring_nf
  · ring_nf

/-- The complementary proportion of exponent classes certified by the sieve
tends to one. -/
noncomputable def certifiedClassProportion (n : ℕ) : ℝ :=
  1 - uncertifiedClassProportion n

theorem tendsto_certifiedClassProportion :
    Filter.Tendsto certifiedClassProportion Filter.atTop (nhds 1) := by
  have hone :
      Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  unfold certifiedClassProportion
  convert hone.sub tendsto_uncertifiedClassProportion using 1
  norm_num

/-- A certificate for the reduced exponent class propagates to every exponent
in that congruence class and proves divisibility by nine. -/
theorem nine_dvd_centralBinom_two_pow_of_reduced_carry_certificate
    (n k : ℕ)
    (hcarry :
      2 ≤ ternaryDoubleCarryCount
        (Nat.digits 3
          (2 ^ (k % (2 * 3 ^ (n + 2))) % 3 ^ (n + 3)))) :
    9 ∣ Nat.centralBinom (2 ^ k) := by
  apply nine_dvd_centralBinom_of_modular_carry_certificate (depth := n + 3)
  rw [two_pow_mod_three_pow_succ_eq_reduced_exponent (n + 2) k]
  exact hcarry

/-- Every certified class denotes an infinite congruence class of GKP inputs
whose central binomial coefficients are divisible by nine. -/
theorem nine_dvd_centralBinom_two_pow_of_certified_class
    (n k : ℕ) (exponentClass : CertifiedExponentClasses n)
    (hk : k % (2 * 3 ^ (n + 2)) = exponentClass.val.val) :
    9 ∣ Nat.centralBinom (2 ^ k) := by
  apply nine_dvd_centralBinom_two_pow_of_reduced_carry_certificate n k
  simpa [hk] using exponentClass.property

/-- The same certified classes avoid the deficient-carry language appearing
in the exact GKP characterization. -/
theorem badCarryLanguage_two_pow_eq_false_of_certified_class
    (n k : ℕ) (exponentClass : CertifiedExponentClasses n)
    (hk : k % (2 * 3 ^ (n + 2)) = exponentClass.val.val) :
    badCarryLanguage (Nat.digits 3 (2 ^ k)) = false := by
  have hdiv := nine_dvd_centralBinom_two_pow_of_certified_class
    n k exponentClass hk
  cases hbad : badCarryLanguage (Nat.digits 3 (2 ^ k)) with
  | false => rfl
  | true =>
      exact False.elim
        ((badCarryLanguage_digits_true_iff_not_nine_dvd (2 ^ k)).mp hbad hdiv)

/-- **Exact all-depth modular GKP sieve.** At every depth, the theorem gives
the exact number of certified exponent classes and proves the GKP divisibility
conclusion on every exponent in each such class. -/
theorem gkp_exact_modular_sieve (n : ℕ) :
    Fintype.card (CertifiedExponentClasses n) =
        2 * 3 ^ (n + 2) - (n + 9) * 2 ^ n ∧
      ∀ exponentClass : CertifiedExponentClasses n,
        ∀ k : ℕ,
          k % (2 * 3 ^ (n + 2)) = exponentClass.val.val →
            9 ∣ Nat.centralBinom (2 ^ k) ∧
              badCarryLanguage (Nat.digits 3 (2 ^ k)) = false := by
  exact ⟨card_certifiedExponentClasses n,
    fun exponentClass k hk =>
      ⟨nine_dvd_centralBinom_two_pow_of_certified_class
          n k exponentClass hk,
        badCarryLanguage_two_pow_eq_false_of_certified_class
          n k exponentClass hk⟩⟩

end GKPCarry
