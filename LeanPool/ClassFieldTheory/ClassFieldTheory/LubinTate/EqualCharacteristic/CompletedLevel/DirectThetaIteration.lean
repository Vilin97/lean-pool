/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaSeries
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaFirstIdentity
/-!
# The completed theta-intertwining theorem: iterating the direct second theta identity

For the direct orientation `T → uT`, this file applies coefficient
Frobenius repeatedly to the formal identity
`theta^φ ∘ e_T = e_(uT) ∘ theta`.
-/

@[expose] public section

noncomputable section

open scoped PowerSeries


namespace LubinTate
namespace EqualCharacteristic

/-- The `i`-fold arithmetic-Frobenius twist of the direct theta series. -/
noncomputable def equalCharacteristicDirectThetaSeriesFrobeniusIterate
    {k : Type*} [Field k] [Finite k] (u : k⟦X⟧ˣ) :
    ℕ → ((AlgebraicClosure k)⟦X⟧)⟦X⟧
  | 0 => equalCharacteristicDirectThetaSeries u
  | i + 1 => PowerSeries.map (equalCharacteristicPowerSeriesFrobenius k)
      (equalCharacteristicDirectThetaSeriesFrobeniusIterate u i)

/-- States the theorem `equalCharacteristicDirectThetaSeriesFrobeniusIterate_zero`. -/
@[simp]
theorem equalCharacteristicDirectThetaSeriesFrobeniusIterate_zero
    {k : Type*} [Field k] [Finite k] (u : k⟦X⟧ˣ) :
    equalCharacteristicDirectThetaSeriesFrobeniusIterate u 0 =
      equalCharacteristicDirectThetaSeries u :=
  rfl

/-- States the theorem `equalCharacteristicDirectThetaSeriesFrobeniusIterate_succ`. -/
@[simp]
theorem equalCharacteristicDirectThetaSeriesFrobeniusIterate_succ
    {k : Type*} [Field k] [Finite k] (u : k⟦X⟧ˣ) (i : ℕ) :
    equalCharacteristicDirectThetaSeriesFrobeniusIterate u (i + 1) =
      PowerSeries.map (equalCharacteristicPowerSeriesFrobenius k)
        (equalCharacteristicDirectThetaSeriesFrobeniusIterate u i) :=
  rfl

/-- States the theorem `equalCharacteristicDirectThetaSeriesFrobeniusIterate_constantCoeff`. -/
@[simp]
theorem equalCharacteristicDirectThetaSeriesFrobeniusIterate_constantCoeff
    {k : Type*} [Field k] [Finite k] (u : k⟦X⟧ˣ) (i : ℕ) :
    PowerSeries.constantCoeff
      (equalCharacteristicDirectThetaSeriesFrobeniusIterate u i) = 0 := by
  induction i with
  | zero => exact equalCharacteristicDirectThetaSeries_constantCoeff u
  | succ i ih =>
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply] at ih ⊢
      rw [equalCharacteristicDirectThetaSeriesFrobeniusIterate_succ,
        PowerSeries.coeff_map, ih, map_zero]

/-- States the theorem `equalCharacteristicDirectThetaSeriesFrobeniusIterate_hasSubst`. -/
theorem equalCharacteristicDirectThetaSeriesFrobeniusIterate_hasSubst
    {k : Type*} [Field k] [Finite k] (u : k⟦X⟧ˣ) (i : ℕ) :
    PowerSeries.HasSubst
      (equalCharacteristicDirectThetaSeriesFrobeniusIterate u i) :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    (equalCharacteristicDirectThetaSeriesFrobeniusIterate_constantCoeff u i)

private theorem equalCharacteristicDirectCompletedTargetUniformizer_frobenius
    {k : Type*} [Field k] [Finite k] (u : k⟦X⟧ˣ) :
    equalCharacteristicPowerSeriesFrobenius k
        (equalCharacteristicDirectCompletedTargetUniformizer u) =
      equalCharacteristicDirectCompletedTargetUniformizer u := by
  simp [equalCharacteristicDirectCompletedTargetUniformizer,
    equalCharacteristicPowerSeriesFrobenius_map_algebraMap]

private theorem equalCharacteristicDirectCompletedLubinTateSeries_map_frobenius
    {k : Type*} [Field k] [Finite k]
    (pi : (AlgebraicClosure k)⟦X⟧) :
    PowerSeries.map (equalCharacteristicPowerSeriesFrobenius k)
        (equalCharacteristicCompletedLubinTateSeries (k := k) pi) =
      equalCharacteristicCompletedLubinTateSeries (k := k)
        (equalCharacteristicPowerSeriesFrobenius k pi) := by
  simp [equalCharacteristicCompletedLubinTateSeries]

private theorem equalCharacteristicDirectSourceLubinTateSeries_frobenius
    {k : Type*} [Field k] [Finite k] :
    PowerSeries.map (equalCharacteristicPowerSeriesFrobenius k)
        (equalCharacteristicCompletedLubinTateSeries (k := k)
          (PowerSeries.X : (AlgebraicClosure k)⟦X⟧)) =
      equalCharacteristicCompletedLubinTateSeries (k := k) PowerSeries.X := by
  rw [equalCharacteristicDirectCompletedLubinTateSeries_map_frobenius,
    equalCharacteristicPowerSeriesFrobenius_X]

private theorem equalCharacteristicDirectTargetLubinTateSeries_frobenius
    {k : Type*} [Field k] [Finite k] (u : k⟦X⟧ˣ) :
    PowerSeries.map (equalCharacteristicPowerSeriesFrobenius k)
        (equalCharacteristicCompletedLubinTateSeries (k := k)
          (equalCharacteristicDirectCompletedTargetUniformizer u)) =
      equalCharacteristicCompletedLubinTateSeries (k := k)
        (equalCharacteristicDirectCompletedTargetUniformizer u) := by
  rw [equalCharacteristicDirectCompletedLubinTateSeries_map_frobenius,
    equalCharacteristicDirectCompletedTargetUniformizer_frobenius]

/-- Every direct Frobenius twist intertwines the next source and target
Lubin--Tate steps. -/
theorem equalCharacteristicDirectThetaSeriesFrobeniusIterate_intertwines
    {k : Type*} [Field k] [Finite k] (u : k⟦X⟧ˣ) (i : ℕ) :
    PowerSeries.subst
        (equalCharacteristicCompletedLubinTateSeries (k := k)
          (PowerSeries.X : (AlgebraicClosure k)⟦X⟧))
        (equalCharacteristicDirectThetaSeriesFrobeniusIterate u (i + 1)) =
      PowerSeries.subst
        (equalCharacteristicDirectThetaSeriesFrobeniusIterate u i)
        (equalCharacteristicCompletedLubinTateSeries (k := k)
          (equalCharacteristicDirectCompletedTargetUniformizer u)) := by
  induction i with
  | zero =>
      simpa [equalCharacteristicDirectThetaSeriesFrobeniusIterate_succ,
        equalCharacteristicDirectThetaSeriesFrobenius]
        using equalCharacteristicDirectThetaSeries_intertwines u
  | succ i ih =>
      have h := congrArg
        (PowerSeries.map (equalCharacteristicPowerSeriesFrobenius k)) ih
      change
        (PowerSeries.subst
          (equalCharacteristicCompletedLubinTateSeries (k := k)
            (PowerSeries.X : (AlgebraicClosure k)⟦X⟧))
          (equalCharacteristicDirectThetaSeriesFrobeniusIterate
            u (i + 1))).map
              (equalCharacteristicPowerSeriesFrobenius k) =
        (PowerSeries.subst
          (equalCharacteristicDirectThetaSeriesFrobeniusIterate u i)
          (equalCharacteristicCompletedLubinTateSeries (k := k)
            (equalCharacteristicDirectCompletedTargetUniformizer u))).map
              (equalCharacteristicPowerSeriesFrobenius k) at h
      rw [PowerSeries.map_subst
          (equalCharacteristicCompletedLubinTateSeries_hasSubst
            (PowerSeries.X : (AlgebraicClosure k)⟦X⟧)),
        PowerSeries.map_subst
          (equalCharacteristicDirectThetaSeriesFrobeniusIterate_hasSubst
            u i)] at h
      have hsource :
          MvPowerSeries.map (equalCharacteristicPowerSeriesFrobenius k)
              (equalCharacteristicCompletedLubinTateSeries (k := k)
                (PowerSeries.X : (AlgebraicClosure k)⟦X⟧)) =
            equalCharacteristicCompletedLubinTateSeries (k := k)
              PowerSeries.X := by
        change PowerSeries.map (equalCharacteristicPowerSeriesFrobenius k)
            (equalCharacteristicCompletedLubinTateSeries (k := k)
              (PowerSeries.X : (AlgebraicClosure k)⟦X⟧)) = _
        exact equalCharacteristicDirectSourceLubinTateSeries_frobenius
      have htwist :
          MvPowerSeries.map (equalCharacteristicPowerSeriesFrobenius k)
              (equalCharacteristicDirectThetaSeriesFrobeniusIterate u i) =
            equalCharacteristicDirectThetaSeriesFrobeniusIterate u (i + 1) := by
        change PowerSeries.map (equalCharacteristicPowerSeriesFrobenius k)
            (equalCharacteristicDirectThetaSeriesFrobeniusIterate u i) = _
        exact
          (equalCharacteristicDirectThetaSeriesFrobeniusIterate_succ u i).symm
      rw [hsource, htwist,
        equalCharacteristicDirectTargetLubinTateSeries_frobenius] at h
      simpa only [← equalCharacteristicDirectThetaSeriesFrobeniusIterate_succ]
        using h

end EqualCharacteristic
end LubinTate
