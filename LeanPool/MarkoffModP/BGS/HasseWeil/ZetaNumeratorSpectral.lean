/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.PolynomialSpectral

/-!
# From a zeta numerator to a rank-bounded spectral formula

The zeta numerator of a curve need not be presented with an even degree in
the coarse plane-curve estimates used by this project.  This file therefore
states the spectral argument for an arbitrary finite rank.  Its final bound
is `rank * sqrt q`.

`HasZetaNumeratorPointCountFormula` is a transparent property of a concrete
polynomial: its reciprocal-root power sums are the extension point-count
errors.  The zeta-function construction must prove that property; it is not
an assumed theorem or a replacement for Hasse--Weil.
-/

@[expose] public section

namespace BGS.HasseWeil

open Filter Asymptotics
open scoped BigOperators

noncomputable section

/-- A compatible spectral formula with an arbitrary finite number of
parameters. -/
def HasExtensionPointCountSpectralFormulaOfRank
    (q rank : ℕ) (pointCount : ℕ → ℕ) (alpha : Fin rank → ℂ) : Prop :=
  ∀ m, 0 < m →
    (pointCount m : ℂ) = (q : ℂ) ^ m + 1 - ∑ i, alpha i ^ m

/-- The logarithmic-derivative point-count identity for a normalized zeta
numerator, written directly as reciprocal-root power sums. -/
def HasZetaNumeratorPointCountFormula
    (q : ℕ) (pointCount : ℕ → ℕ) (P : Polynomial ℂ) : Prop :=
  P.coeff 0 = 1 ∧
    ∀ m, 0 < m →
      (pointCount m : ℂ) = (q : ℂ) ^ m + 1 -
        (P.roots.map fun r => r⁻¹ ^ m).sum

/-- A zeta-numerator point-count identity gives a spectral formula indexed by
the numerator degree. -/
theorem hasExtensionPointCountSpectralFormulaOfRank_of_zetaNumerator
    {q : ℕ} {pointCount : ℕ → ℕ} {P : Polynomial ℂ}
    (h : HasZetaNumeratorPointCountFormula q pointCount P) :
    HasExtensionPointCountSpectralFormulaOfRank q P.natDegree pointCount
      (reciprocalRootParameter P) := by
  intro m hm
  rw [sum_reciprocalRootParameter_pow]
  exact h.2 m hm

/-- Extension-count error of order `q^n` gives the corresponding even
power-sum estimate, for arbitrary spectral rank. -/
theorem evenPowerSum_isBigO_of_extensionPointCountError_isBigO_of_rank
    {q rank : ℕ} {pointCount : ℕ → ℕ} {alpha : Fin rank → ℂ}
    (hformula :
      HasExtensionPointCountSpectralFormulaOfRank q rank pointCount alpha)
    (herror :
      (fun n : ℕ ↦
        (pointCount (2 * n) : ℂ) - (q : ℂ) ^ (2 * n) - 1) =O[atTop]
          fun n : ℕ ↦ (q : ℝ) ^ n) :
    (fun n : ℕ ↦ ∑ i, alpha i ^ (2 * n)) =O[atTop]
      fun n : ℕ ↦ (q : ℝ) ^ n := by
  apply herror.neg_left.congr'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hpositive : 0 < 2 * n := by omega
    have h := hformula (2 * n) hpositive
    change -((pointCount (2 * n) : ℂ) - (q : ℂ) ^ (2 * n) - 1) =
      ∑ i, alpha i ^ (2 * n)
    rw [h]
    ring
  · exact Filter.EventuallyEq.rfl

/-- An extension-count error estimate along any fixed positive
`2 * δ`-divisible subsequence gives the corresponding power-sum estimate,
for arbitrary spectral rank. -/
theorem divisibleEvenPowerSum_isBigO_of_extensionPointCountError_isBigO_of_rank
    {q rank δ : ℕ} {pointCount : ℕ → ℕ} {alpha : Fin rank → ℂ}
    (hδ : 0 < δ)
    (hformula :
      HasExtensionPointCountSpectralFormulaOfRank q rank pointCount alpha)
    (herror :
      (fun n : ℕ ↦
        (pointCount (2 * δ * n) : ℂ) - (q : ℂ) ^ (2 * δ * n) - 1) =O[atTop]
          fun n : ℕ ↦ ((q : ℝ) ^ δ) ^ n) :
    (fun n : ℕ ↦ ∑ i, alpha i ^ (2 * δ * n)) =O[atTop]
      fun n : ℕ ↦ ((q : ℝ) ^ δ) ^ n := by
  apply herror.neg_left.congr'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hpositive : 0 < 2 * δ * n :=
      Nat.mul_pos (Nat.mul_pos (by omega) hδ) hn
    have h := hformula (2 * δ * n) hpositive
    change -((pointCount (2 * δ * n) : ℂ) -
        (q : ℂ) ^ (2 * δ * n) - 1) =
      ∑ i, alpha i ^ (2 * δ * n)
    rw [h]
    ring
  · exact Filter.EventuallyEq.rfl

/-- The arbitrary-rank analytic Hasse step. -/
theorem abs_pointCount_sub_card_sub_one_le_of_rank_extensionFormula_and_evenError_isBigO
    (q rank : ℕ) (pointCount : ℕ → ℕ) (alpha : Fin rank → ℂ)
    (hformula :
      HasExtensionPointCountSpectralFormulaOfRank q rank pointCount alpha)
    (herror :
      (fun n : ℕ ↦
        (pointCount (2 * n) : ℂ) - (q : ℂ) ^ (2 * n) - 1) =O[atTop]
          fun n : ℕ ↦ (q : ℝ) ^ n) :
    |(pointCount 1 : ℝ) - q - 1| ≤ (rank : ℝ) * Real.sqrt q := by
  have hnorm : ∀ i, ‖alpha i‖ ≤ Real.sqrt q :=
    spectral_norm_le_sqrt_of_evenPowerSum_isBigO alpha (by positivity)
      (evenPowerSum_isBigO_of_extensionPointCountError_isBigO_of_rank
        hformula herror)
  have hone := hformula 1 (by omega)
  have herrorOne :
      (((pointCount 1 : ℝ) - q - 1 : ℝ) : ℂ) = -(∑ i, alpha i) := by
    push_cast
    rw [hone]
    simp
    ring
  calc
    |(pointCount 1 : ℝ) - q - 1| =
        ‖(((pointCount 1 : ℝ) - q - 1 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖∑ i, alpha i‖ := by rw [herrorOne, norm_neg]
    _ ≤ ∑ i, ‖alpha i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin rank, Real.sqrt q := by
      exact Finset.sum_le_sum fun i _ => hnorm i
    _ = (rank : ℝ) * Real.sqrt q := by simp

/-- The arbitrary-rank analytic Hasse step from an estimate available only
along a fixed positive divisible-even subsequence. -/
theorem
    abs_pointCount_sub_card_sub_one_le_of_rank_extensionFormula_and_divisibleEvenError_isBigO
    (q rank δ : ℕ) (pointCount : ℕ → ℕ) (alpha : Fin rank → ℂ)
    (hq : 0 < q) (hδ : 0 < δ)
    (hformula :
      HasExtensionPointCountSpectralFormulaOfRank q rank pointCount alpha)
    (herror :
      (fun n : ℕ ↦
        (pointCount (2 * δ * n) : ℂ) - (q : ℂ) ^ (2 * δ * n) - 1) =O[atTop]
          fun n : ℕ ↦ ((q : ℝ) ^ δ) ^ n) :
    |(pointCount 1 : ℝ) - q - 1| ≤ (rank : ℝ) * Real.sqrt q := by
  have hnorm : ∀ i, ‖alpha i‖ ≤ Real.sqrt q :=
    spectral_norm_le_sqrt_of_divisibleEvenPowerSum_isBigO alpha
      (by exact_mod_cast hq) hδ
      (divisibleEvenPowerSum_isBigO_of_extensionPointCountError_isBigO_of_rank
        hδ hformula herror)
  have hone := hformula 1 (by omega)
  have herrorOne :
      (((pointCount 1 : ℝ) - q - 1 : ℝ) : ℂ) = -(∑ i, alpha i) := by
    push_cast
    rw [hone]
    simp
    ring
  calc
    |(pointCount 1 : ℝ) - q - 1| =
        ‖(((pointCount 1 : ℝ) - q - 1 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖∑ i, alpha i‖ := by rw [herrorOne, norm_neg]
    _ ≤ ∑ i, ‖alpha i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin rank, Real.sqrt q := by
      exact Finset.sum_le_sum fun i _ => hnorm i
    _ = (rank : ℝ) * Real.sqrt q := by simp

/-- A normalized zeta numerator and the even extension estimate imply the
base-field Hasse bound with coefficient equal to the numerator degree. -/
theorem abs_pointCount_sub_card_sub_one_le_of_zetaNumerator_and_evenError_isBigO
    (q : ℕ) (pointCount : ℕ → ℕ) (P : Polynomial ℂ)
    (hformula : HasZetaNumeratorPointCountFormula q pointCount P)
    (herror :
      (fun n : ℕ ↦
        (pointCount (2 * n) : ℂ) - (q : ℂ) ^ (2 * n) - 1) =O[atTop]
          fun n : ℕ ↦ (q : ℝ) ^ n) :
    |(pointCount 1 : ℝ) - q - 1| ≤
      (P.natDegree : ℝ) * Real.sqrt q := by
  exact abs_pointCount_sub_card_sub_one_le_of_rank_extensionFormula_and_evenError_isBigO
    q P.natDegree pointCount (reciprocalRootParameter P)
      (hasExtensionPointCountSpectralFormulaOfRank_of_zetaNumerator hformula) herror

/-- A normalized zeta numerator and a square-root error estimate along a
fixed positive divisible-even subsequence imply the base-field Hasse bound,
with coefficient equal to the numerator degree. -/
theorem
    abs_pointCount_sub_card_sub_one_le_of_zetaNumerator_and_divisibleEvenError_isBigO
    (q δ : ℕ) (pointCount : ℕ → ℕ) (P : Polynomial ℂ)
    (hq : 0 < q) (hδ : 0 < δ)
    (hformula : HasZetaNumeratorPointCountFormula q pointCount P)
    (herror :
      (fun n : ℕ ↦
        (pointCount (2 * δ * n) : ℂ) - (q : ℂ) ^ (2 * δ * n) - 1) =O[atTop]
          fun n : ℕ ↦ ((q : ℝ) ^ δ) ^ n) :
    |(pointCount 1 : ℝ) - q - 1| ≤
      (P.natDegree : ℝ) * Real.sqrt q := by
  exact
    abs_pointCount_sub_card_sub_one_le_of_rank_extensionFormula_and_divisibleEvenError_isBigO
      q P.natDegree δ pointCount (reciprocalRootParameter P) hq hδ
      (hasExtensionPointCountSpectralFormulaOfRank_of_zetaNumerator hformula) herror

end

end BGS.HasseWeil
