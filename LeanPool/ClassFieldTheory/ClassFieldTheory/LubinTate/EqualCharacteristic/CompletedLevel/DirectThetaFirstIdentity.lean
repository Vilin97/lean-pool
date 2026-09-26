/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaSeries
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectLubinTateBracket
/-!
# First theta identity for the completed change of parameter

For the standard source prime `T` and target prime `uT`, this file proves

`theta^φ = theta ∘ [u]`.

The bracket `[u]` is the independently constructed endomorphism of the
standard Lubin--Tate group from `EqualCharacteristicDirectLubinTateBracket`.
The proof follows the uniqueness argument: both sides have
the same linear coefficient and satisfy the same contracting coefficient
recursion.
-/

@[expose] public section

noncomputable
section

open scoped PowerSeries


universe u

namespace LubinTate
namespace EqualCharacteristic

variable {k : Type u} [Field k] [Finite k]

/-- Coefficients of the formal composite `theta ∘ [u]`. -/
noncomputable def equalCharacteristicDirectThetaAfterBracketCoefficient
    (u : k⟦X⟧ˣ) : ℕ → (AlgebraicClosure k)⟦X⟧ :=
  equalCharacteristicQAdditiveCompositionCoefficient (k := k)
    (equalCharacteristicDirectThetaCoefficient u)
    (equalCharacteristicCompletedDirectBracketCoefficient (u : k⟦X⟧))

/-- The composite `theta ∘ [u]` written as a sparse `q`-additive series. -/
theorem equalCharacteristicDirectThetaSeries_subst_directBracket
    (u : k⟦X⟧ˣ) :
    PowerSeries.subst
        (equalCharacteristicCompletedDirectBracket (u : k⟦X⟧))
        (equalCharacteristicDirectThetaSeries u) =
      equalCharacteristicQAdditiveSeries k
        (equalCharacteristicDirectThetaAfterBracketCoefficient u) := by
  exact equalCharacteristicQAdditiveSeries_subst_qAdditiveSeries
    (k := k) (equalCharacteristicDirectThetaCoefficient u)
    (equalCharacteristicCompletedDirectBracketCoefficient (u : k⟦X⟧))

/-- The linear term of `theta ∘ [u]` is `φ(b₀)`. -/
theorem equalCharacteristicDirectThetaAfterBracketCoefficient_zero
    (u : k⟦X⟧ˣ) :
    equalCharacteristicDirectThetaAfterBracketCoefficient u 0 =
      equalCharacteristicPowerSeriesFrobenius k
        (equalCharacteristicDirectThetaCoefficient u 0) := by
  have hsemi := equalCharacteristicPowerSeriesFrobenius_semilinearUnit
    (k := k) (u : k⟦X⟧)
      (by
        intro hzero
        have hunit := PowerSeries.isUnit_constantCoeff (u : k⟦X⟧) u.isUnit
        apply hunit.ne_zero
        simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hzero)
  rw [equalCharacteristicDirectThetaCoefficient_zero]
  simpa [equalCharacteristicDirectThetaAfterBracketCoefficient,
    equalCharacteristicQAdditiveCompositionCoefficient,
    equalCharacteristicCompletedDirectBracketCoefficient] using
      (mul_comm _ _).trans hsemi.symm

/-- Since `[u]` is Frobenius-fixed and commutes with `e_T`, the composite
`theta ∘ [u]` satisfies theta's direct Frobenius-intertwining equation. -/
theorem equalCharacteristicDirectThetaSeries_subst_directBracket_intertwines
    (u : k⟦X⟧ˣ) :
    PowerSeries.subst
        (equalCharacteristicCompletedLubinTateSeries (k := k)
          (PowerSeries.X : (AlgebraicClosure k)⟦X⟧))
        (PowerSeries.map (equalCharacteristicPowerSeriesFrobenius k)
          (PowerSeries.subst
            (equalCharacteristicCompletedDirectBracket (u : k⟦X⟧))
            (equalCharacteristicDirectThetaSeries u))) =
      PowerSeries.subst
        (PowerSeries.subst
          (equalCharacteristicCompletedDirectBracket (u : k⟦X⟧))
          (equalCharacteristicDirectThetaSeries u))
        (equalCharacteristicCompletedLubinTateSeries (k := k)
          (equalCharacteristicDirectCompletedTargetUniformizer u)) := by
  let H := equalCharacteristicCompletedDirectBracket (u : k⟦X⟧)
  let E := equalCharacteristicCompletedLubinTateSeries (k := k)
    (PowerSeries.X : (AlgebraicClosure k)⟦X⟧)
  let Ebar := equalCharacteristicCompletedLubinTateSeries (k := k)
    (equalCharacteristicDirectCompletedTargetUniformizer u)
  let Theta := equalCharacteristicDirectThetaSeries u
  let ThetaF := equalCharacteristicDirectThetaSeriesFrobenius u
  have hH : PowerSeries.HasSubst H :=
    equalCharacteristicCompletedDirectBracket_hasSubst (u : k⟦X⟧)
  have hE : PowerSeries.HasSubst E :=
    equalCharacteristicCompletedLubinTateSeries_hasSubst
      (PowerSeries.X : (AlgebraicClosure k)⟦X⟧)
  have hTheta : PowerSeries.HasSubst Theta :=
    equalCharacteristicDirectThetaSeries_hasSubst u
  have hmap :
      PowerSeries.map (equalCharacteristicPowerSeriesFrobenius k)
          (PowerSeries.subst H Theta) =
        PowerSeries.subst H ThetaF := by
    change (PowerSeries.subst H Theta).map
        (equalCharacteristicPowerSeriesFrobenius k) = _
    rw [PowerSeries.map_subst hH]
    have hHfixed :
        PowerSeries.map (equalCharacteristicPowerSeriesFrobenius k) H = H := by
      simpa only [H] using
        equalCharacteristicCompletedDirectBracket_frobenius (u : k⟦X⟧)
    change MvPowerSeries.map
        (equalCharacteristicPowerSeriesFrobenius k) H = H at hHfixed
    rw [hHfixed]
    rfl
  change PowerSeries.subst E
      (PowerSeries.map (equalCharacteristicPowerSeriesFrobenius k)
        (PowerSeries.subst H Theta)) =
    PowerSeries.subst (PowerSeries.subst H Theta) Ebar
  calc
    _ = PowerSeries.subst E (PowerSeries.subst H ThetaF) := by rw [hmap]
    _ = PowerSeries.subst (PowerSeries.subst E H) ThetaF :=
      PowerSeries.subst_comp_subst_apply hH hE ThetaF
    _ = PowerSeries.subst (PowerSeries.subst H E) ThetaF := by
      rw [equalCharacteristicCompletedDirectBracket_commutes (u : k⟦X⟧)]
    _ = PowerSeries.subst H (PowerSeries.subst E ThetaF) :=
      (PowerSeries.subst_comp_subst_apply hE hH ThetaF).symm
    _ = PowerSeries.subst H (PowerSeries.subst Theta Ebar) := by
      rw [equalCharacteristicDirectThetaSeries_intertwines u]
    _ = PowerSeries.subst (PowerSeries.subst H Theta) Ebar :=
      PowerSeries.subst_comp_subst_apply hTheta hH Ebar

/-- Coefficient form of a direct-orientation Frobenius intertwiner. -/
theorem equalCharacteristicDirectQAdditiveIntertwiner_succ_comparison
    (u : k⟦X⟧ˣ)
    (c : ℕ → (AlgebraicClosure k)⟦X⟧)
    (hintertwines :
      PowerSeries.subst
          (equalCharacteristicCompletedLubinTateSeries (k := k)
            (PowerSeries.X : (AlgebraicClosure k)⟦X⟧))
          (equalCharacteristicQAdditiveSeries k
            (fun i ↦ equalCharacteristicPowerSeriesFrobenius k (c i))) =
        PowerSeries.subst (equalCharacteristicQAdditiveSeries k c)
          (equalCharacteristicCompletedLubinTateSeries (k := k)
            (equalCharacteristicDirectCompletedTargetUniformizer u)))
    (j : ℕ) :
    equalCharacteristicDirectCompletedTargetUniformizer u * c (j + 1) -
        PowerSeries.X ^ (Nat.card k ^ (j + 1)) *
          equalCharacteristicPowerSeriesFrobenius k (c (j + 1)) =
      equalCharacteristicPowerSeriesFrobenius k (c j) -
        c j ^ Nat.card k := by
  rw [equalCharacteristicQAdditiveSeries_subst_completedLubinTateSeries,
    equalCharacteristicCompletedLubinTateSeries_subst_qAdditiveSeries]
    at hintertwines
  have hcoeff := congrArg
    (PowerSeries.coeff (Nat.card k ^ (j + 1))) hintertwines
  rw [equalCharacteristicQAdditiveSeries_coeff_pow,
    equalCharacteristicQAdditiveSeries_coeff_pow,
    equalCharacteristicLubinTateSubstitutionCoefficient,
    equalCharacteristicLubinTatePostcompositionCoefficient] at hcoeff
  linear_combination -hcoeff

/-- Direct-orientation intertwiners with the same linear coefficient are
equal.  At every higher coefficient this is exactly the uniqueness clause of
the contracting Frobenius equation. -/
theorem equalCharacteristicDirectQAdditiveIntertwinerCoefficient_unique
    (u : k⟦X⟧ˣ)
    (c d : ℕ → (AlgebraicClosure k)⟦X⟧)
    (hzero : c 0 = d 0)
    (hc : ∀ j : ℕ,
      equalCharacteristicDirectCompletedTargetUniformizer u * c (j + 1) -
          PowerSeries.X ^ (Nat.card k ^ (j + 1)) *
            equalCharacteristicPowerSeriesFrobenius k (c (j + 1)) =
        equalCharacteristicPowerSeriesFrobenius k (c j) -
          c j ^ Nat.card k)
    (hd : ∀ j : ℕ,
      equalCharacteristicDirectCompletedTargetUniformizer u * d (j + 1) -
          PowerSeries.X ^ (Nat.card k ^ (j + 1)) *
            equalCharacteristicPowerSeriesFrobenius k (d (j + 1)) =
        equalCharacteristicPowerSeriesFrobenius k (d j) -
          d j ^ Nat.card k) :
    c = d := by
  funext j
  induction j with
  | zero => exact hzero
  | succ j ih =>
      have hcj := hc j
      have hdj := hd j
      rw [ih] at hcj
      let delta := c (j + 1) - d (j + 1)
      have hdiff :
          equalCharacteristicDirectCompletedTargetUniformizer u * delta -
              PowerSeries.X ^ (Nat.card k ^ (j + 1)) *
                equalCharacteristicPowerSeriesFrobenius k delta = 0 := by
        dsimp only [delta]
        rw [map_sub]
        linear_combination hcj - hdj
      have hmul :
          equalCharacteristicDirectCompletedTargetUniformizer u *
              (delta - equalCharacteristicDirectThetaGamma u (j + 1) *
                equalCharacteristicPowerSeriesFrobenius k delta) = 0 := by
        rw [mul_sub, ← mul_assoc,
          equalCharacteristicDirectTargetUniformizer_mul_gamma u
            (j + 1) (Nat.zero_lt_succ j)]
        exact hdiff
      have htarget :
          equalCharacteristicDirectCompletedTargetUniformizer u ≠ 0 := by
        rw [equalCharacteristicDirectCompletedTargetUniformizer]
        exact mul_ne_zero
          ((u.isUnit.map
            (PowerSeries.map (algebraMap k (AlgebraicClosure k)))).ne_zero)
          (PowerSeries.X_ne_zero (R := AlgebraicClosure k))
      have hhom :
          delta - equalCharacteristicDirectThetaGamma u (j + 1) *
              equalCharacteristicPowerSeriesFrobenius k delta = 0 := by
        exact mul_left_cancel₀ htarget (by simpa using hmul)
      have hgamma := equalCharacteristicDirectThetaGamma_constantCoeff u
        (j + 1) (Nat.zero_lt_succ j)
      have hunique := existsUnique_contractingFrobeniusEquation
        (equalCharacteristicCoefficientFrobenius k).toRingHom
        (equalCharacteristicDirectThetaGamma u (j + 1)) 0 hgamma
      have hzeroSolution :
          (0 : (AlgebraicClosure k)⟦X⟧) -
              equalCharacteristicDirectThetaGamma u (j + 1) *
                equalCharacteristicPowerSeriesFrobenius k 0 = 0 := by
        simp
      have hdelta : delta = 0 :=
        hunique.unique hhom hzeroSolution
      exact sub_eq_zero.mp (by simpa only [delta] using hdelta)

/-- The target prime `uT` is fixed by arithmetic Frobenius. -/
theorem equalCharacteristicDirectCompletedTargetUniformizer_frobenius
    (u : k⟦X⟧ˣ) :
    equalCharacteristicPowerSeriesFrobenius k
        (equalCharacteristicDirectCompletedTargetUniformizer u) =
      equalCharacteristicDirectCompletedTargetUniformizer u := by
  rw [equalCharacteristicDirectCompletedTargetUniformizer, map_mul,
    equalCharacteristicPowerSeriesFrobenius_map_algebraMap,
    equalCharacteristicPowerSeriesFrobenius_X]

/-- Applying Frobenius to theta's coefficient comparison gives the recursion
for the coefficients of `theta^φ`. -/
theorem equalCharacteristicDirectThetaFrobeniusCoefficient_succ_comparison
    (u : k⟦X⟧ˣ) (j : ℕ) :
    equalCharacteristicDirectCompletedTargetUniformizer u *
          equalCharacteristicPowerSeriesFrobenius k
            (equalCharacteristicDirectThetaCoefficient u (j + 1)) -
        PowerSeries.X ^ (Nat.card k ^ (j + 1)) *
          equalCharacteristicPowerSeriesFrobenius k
            (equalCharacteristicPowerSeriesFrobenius k
              (equalCharacteristicDirectThetaCoefficient u (j + 1))) =
      equalCharacteristicPowerSeriesFrobenius k
          (equalCharacteristicPowerSeriesFrobenius k
            (equalCharacteristicDirectThetaCoefficient u j)) -
        equalCharacteristicPowerSeriesFrobenius k
            (equalCharacteristicDirectThetaCoefficient u j) ^ Nat.card k := by
  have h := congrArg (equalCharacteristicPowerSeriesFrobenius k)
    (equalCharacteristicDirectThetaCoefficient_succ_comparison u j)
  simpa [map_sub, map_mul, map_pow,
    equalCharacteristicPowerSeriesFrobenius_X,
    equalCharacteristicDirectCompletedTargetUniformizer_frobenius] using h

/-- Coefficients of `theta ∘ [u]` obey the same direct recursion. -/
theorem equalCharacteristicDirectThetaAfterBracketCoefficient_succ_comparison
    (u : k⟦X⟧ˣ) (j : ℕ) :
    equalCharacteristicDirectCompletedTargetUniformizer u *
          equalCharacteristicDirectThetaAfterBracketCoefficient u (j + 1) -
        PowerSeries.X ^ (Nat.card k ^ (j + 1)) *
          equalCharacteristicPowerSeriesFrobenius k
            (equalCharacteristicDirectThetaAfterBracketCoefficient u (j + 1)) =
      equalCharacteristicPowerSeriesFrobenius k
          (equalCharacteristicDirectThetaAfterBracketCoefficient u j) -
        equalCharacteristicDirectThetaAfterBracketCoefficient u j ^ Nat.card k := by
  have hintertwines :=
    equalCharacteristicDirectThetaSeries_subst_directBracket_intertwines u
  rw [equalCharacteristicDirectThetaSeries_subst_directBracket,
    equalCharacteristicQAdditiveSeries_map] at hintertwines
  exact equalCharacteristicDirectQAdditiveIntertwiner_succ_comparison
    u (equalCharacteristicDirectThetaAfterBracketCoefficient u)
      hintertwines j

/-- The completed theta-intertwining theorem, first theta identity in the direct orientation:
`theta^φ = theta ∘ [u]`. -/
theorem equalCharacteristicDirectThetaSeriesFrobenius_eq_subst_directBracket
    (u : k⟦X⟧ˣ) :
    equalCharacteristicDirectThetaSeriesFrobenius u =
      PowerSeries.subst
        (equalCharacteristicCompletedDirectBracket (u : k⟦X⟧))
        (equalCharacteristicDirectThetaSeries u) := by
  have hcoeff :
      (fun j ↦ equalCharacteristicPowerSeriesFrobenius k
        (equalCharacteristicDirectThetaCoefficient u j)) =
      equalCharacteristicDirectThetaAfterBracketCoefficient u :=
    equalCharacteristicDirectQAdditiveIntertwinerCoefficient_unique u
      (fun j ↦ equalCharacteristicPowerSeriesFrobenius k
        (equalCharacteristicDirectThetaCoefficient u j))
      (equalCharacteristicDirectThetaAfterBracketCoefficient u)
      (equalCharacteristicDirectThetaAfterBracketCoefficient_zero u).symm
      (equalCharacteristicDirectThetaFrobeniusCoefficient_succ_comparison u)
      (equalCharacteristicDirectThetaAfterBracketCoefficient_succ_comparison u)
  rw [equalCharacteristicDirectThetaSeriesFrobenius_eq_qAdditiveSeries,
    equalCharacteristicDirectThetaSeries_subst_directBracket]
  exact congrArg (equalCharacteristicQAdditiveSeries k) hcoeff

end EqualCharacteristic
end LubinTate
