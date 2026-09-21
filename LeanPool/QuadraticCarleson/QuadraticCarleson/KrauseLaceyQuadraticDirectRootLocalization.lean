/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectOneOffset

/-!
# Root localization for the direct quadratic proof

The localized tail is supported in its root interval.  This module replaces
the test function by its root indicator, allowing the direct `L²` proof to use
the paper's root-local `p`-mass hypothesis without imposing a global one.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyQuadraticDirectRootLocalization

open KrauseLaceyQuadraticDirectExceptionalPairing
open KrauseLaceyQuadraticDirectLowPairing
open KrauseLaceyQuadraticDirectOneOffset
open KrauseLaceyStoppingRecursion


noncomputable section

/-- Restriction of a bounded compactly supported test function to a real
interval, retained in the same test-function class. -/
def intervalRestrictionL0Infinity (g : L0Infinity)
    (I : RealInterval) : L0Infinity where
  toFun := I.carrier.indicator g
  measurable_toFun := g.measurable_toFun.indicator I.measurableSet_carrier
  bounded_toFun := by
    rcases g.bounded_toFun with ⟨C, hC⟩
    have hC0 : 0 ≤ C := (norm_nonneg (g 0)).trans (hC 0)
    refine ⟨C, fun x ↦ ?_⟩
    by_cases hx : x ∈ I.carrier
    · simpa only [Set.indicator_of_mem hx] using hC x
    · simp only [Set.indicator_of_notMem hx, norm_zero]
      exact hC0
  hasCompactSupport_toFun := by
    apply HasCompactSupport.of_support_subset_isCompact
      g.hasCompactSupport_toFun
    intro x hx
    apply subset_tsupport g
    intro hg
    apply hx
    by_cases hxI : x ∈ I.carrier
    · simp only [Set.indicator_of_mem hxI, hg]
    · simp only [Set.indicator_of_notMem hxI]

@[simp] theorem intervalRestrictionL0Infinity_apply
    (g : L0Infinity) (I : RealInterval) (x : ℝ) :
    intervalRestrictionL0Infinity g I x = I.carrier.indicator g x := rfl

theorem intervalRestrictionL0Infinity_eq_of_mem
    (g : L0Infinity) (I : RealInterval) {x : ℝ} (hx : x ∈ I.carrier) :
    intervalRestrictionL0Infinity g I x = g x := by
  simp only [intervalRestrictionL0Infinity_apply, Set.indicator_of_mem hx]

theorem intervalRestrictionL0Infinity_eq_zero_of_notMem
    (g : L0Infinity) (I : RealInterval) {x : ℝ} (hx : x ∉ I.carrier) :
    intervalRestrictionL0Infinity g I x = 0 := by
  simp only [intervalRestrictionL0Infinity_apply, Set.indicator_of_notMem hx]

/-- The global real `p`-mass of the restricted function is exactly the local
mass of the original function on the interval. -/
theorem integral_norm_rpow_intervalRestrictionL0Infinity
    (g : L0Infinity) (I : RealInterval) {p : ℝ} (hp : 0 < p) :
    (∫ x, ‖intervalRestrictionL0Infinity g I x‖ ^ p) =
      ∫ x in I.carrier, ‖g x‖ ^ p := by
  rw [← integral_indicator I.measurableSet_carrier]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ I.carrier
  · simp only [intervalRestrictionL0Infinity_eq_of_mem g I hx,
      Set.indicator_of_mem hx]
  · simp only [intervalRestrictionL0Infinity_eq_zero_of_notMem g I hx,
      norm_zero, Real.zero_rpow hp.ne', Set.indicator_of_notMem hx]

/-- Extended-nonnegative form of the preceding exact mass identity. -/
theorem lintegral_ofReal_norm_rpow_intervalRestrictionL0Infinity
    (g : L0Infinity) (I : RealInterval) {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, ENNReal.ofReal
      (‖intervalRestrictionL0Infinity g I x‖ ^ p)) =
        ENNReal.ofReal (∫ x in I.carrier, ‖g x‖ ^ p) := by
  have hint : Integrable (fun x ↦
      ‖intervalRestrictionL0Infinity g I x‖ ^ p) :=
    KrauseLaceyQuadraticDirectExceptionalPairing.L0Infinity.integrable_norm_rpow_direct
      (intervalRestrictionL0Infinity g I) hp
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun x ↦ Real.rpow_nonneg (norm_nonneg _) _)]
  congr 1
  exact integral_norm_rpow_intervalRestrictionL0Infinity g I hp

/-- Restricting to the root does not change an `L¹` interval average on a
subinterval of that root. -/
theorem intervalL1Average_intervalRestrictionL0Infinity_eq_of_subset
    (g : L0Infinity) {I J : RealInterval}
    (hJI : J.carrier ⊆ I.carrier) :
    intervalL1Average (intervalRestrictionL0Infinity g I) J =
      intervalL1Average g J := by
  unfold intervalL1Average
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem J.measurableSet_carrier] with x hx
  rw [intervalRestrictionL0Infinity_eq_of_mem g I (hJI hx)]

/-- The localized maximal-tail pairing is unchanged by restricting the test
function to the root that contains every selected interval. -/
theorem lintegral_localizedTailMaximal_mul_intervalRestrictionL0Infinity_eq
    {S : Finset RealInterval} (scale : RealInterval → ℤ)
    (f g : L0Infinity) (ell₀ : ℤ) (I₀ : RealInterval)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier) :
    (∫⁻ x, localizedTailMaximal ell₀ scale S f x *
      ‖intervalRestrictionL0Infinity g I₀ x‖ₑ) =
        ∫⁻ x, localizedTailMaximal ell₀ scale S f x * ‖g x‖ₑ := by
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ I₀.carrier
  · rw [intervalRestrictionL0Infinity_eq_of_mem g I₀ hx]
  · rw [localizedTailMaximal_eq_zero_of_notMem
      ell₀ scale S f I₀ hscale hsub hx]
    simp only [zero_mul]

/-- The complete geometric direct quadratic estimate under only the paper's
root-local `p`-mass hypothesis.  No global `p`-mass premise remains. -/
theorem lintegral_localizedTailMaximal_le_directQuadratic_geometric_local
    {S : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (hscaleNonneg : ∀ I ∈ S, 0 ≤ scale I)
    (f : L0Infinity) {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.carrier, ‖f x‖) ≤ M * J.length)
    (I₀ : RealInterval) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (ell₀ : ℤ) (N : ℕ) (hbound : ∀ I ∈ S, scale I < N)
    (g : L0Infinity) {p V F G : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hV : 0 ≤ V)
    (hroot : (∫ x in I₀.carrier, ‖f x‖) ≤ V)
    (hgpRoot : (∫ x in I₀.carrier, ‖g x‖ ^ p) ≤ V)
    (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hfavg : ∀ I ∈ S, intervalL1Average f I ≤ F)
    (hgavg : ∀ I ∈ S, intervalL1Average g I ≤ G) :
    (∫⁻ x, localizedTailMaximal ell₀ scale S f x * ‖g x‖ₑ) ≤
      ((directQuadraticTailEnergyConstant M) ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (8 * positiveDyadicAmplitudeBound) +
          ENNReal.ofReal (8 * positiveDyadicAmplitudeBound * G * F)) *
        ENNReal.ofReal (20 * holderConjugate p * V) := by
  let g₀ := intervalRestrictionL0Infinity g I₀
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hgpGlobal :
      (∫⁻ x, ENNReal.ofReal (‖g₀ x‖ ^ p)) ≤ ENNReal.ofReal V := by
    rw [lintegral_ofReal_norm_rpow_intervalRestrictionL0Infinity g I₀ hp0]
    exact ENNReal.ofReal_le_ofReal hgpRoot
  have hgpRoot₀ : (∫ x in I₀.carrier, ‖g₀ x‖ ^ p) ≤ V := by
    calc
      (∫ x in I₀.carrier, ‖g₀ x‖ ^ p) =
          ∫ x in I₀.carrier, ‖g x‖ ^ p := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem I₀.measurableSet_carrier] with x hx
        rw [intervalRestrictionL0Infinity_eq_of_mem g I₀ hx]
      _ ≤ V := hgpRoot
  have hgavg₀ : ∀ I ∈ S, intervalL1Average g₀ I ≤ G := by
    intro I hI
    rw [intervalL1Average_intervalRestrictionL0Infinity_eq_of_subset
      g (hsub I hI)]
    exact hgavg I hI
  have hlocalized :=
    lintegral_localizedTailMaximal_le_directQuadratic_geometric
      hlam scale hscale hscaleNonneg f hM hmass I₀ hsub ell₀ N hbound
        g₀ hp hp2 hV hroot hgpGlobal hgpRoot₀ hF hG hfavg hgavg₀
  rw [lintegral_localizedTailMaximal_mul_intervalRestrictionL0Infinity_eq
    scale f g ell₀ I₀ hscale hsub] at hlocalized
  exact hlocalized


end
end KrauseLaceyQuadraticDirectRootLocalization
end QuadraticCarleson
