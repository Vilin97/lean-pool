/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.Intertwiner
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.MvPowerSeries.Expand
/-!
# Reduction of a Lubin--Tate intertwining defect

After reduction to the finite residue field, both series become the Frobenius
power series. The two sides of the intertwining equation then agree, so every
coefficient of the defect is divisible by the chosen uniformizer.
-/

noncomputable section

universe u v w

namespace LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

/-- Multivariable finite-field Frobenius: replacing each variable by its
`q`th power is the same as taking the `q`th power of the whole series. -/
theorem mvPowerSeries_expand_natCard
    {k : Type u} [Field k] [Finite k]
    {σ : Type w} [Finite σ] (f : MvPowerSeries σ k) :
    MvPowerSeries.expand (Nat.card k) (Nat.ne_of_gt Nat.card_pos) f =
      f ^ Nat.card k := by
  let : Fintype k := Fintype.ofFinite k
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases FiniteField.card k p with ⟨⟨n, npos⟩, ⟨hpprime, hn⟩⟩
  let : Fact p.Prime := ⟨hpprime⟩
  have hncard : Fintype.card k = p ^ n := by
    simpa using hn
  have hn' : Nat.card k = p ^ n := by
    simpa only [Nat.card_eq_fintype_card] using hncard
  have hpow :
      MvPowerSeries.expand (p ^ n) (pow_ne_zero n hpprime.ne_zero) f =
        f ^ (p ^ n) := by
    rw [← MvPowerSeries.map_iterateFrobenius_expand,
      iterateFrobenius_eq_pow, FiniteField.frobenius_pow hncard,
      RingHom.one_def, MvPowerSeries.map_id]
    · rfl
    · exact hpprime.ne_zero
  simpa only [hn'] using hpow

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

omit [Fintype σ] in
/-- Reduction of `e(X_i)` is `X_i ^ q`. -/
theorem map_inVariable (e : LubinTateSeries F π) (i : σ) :
    MvPowerSeries.map F.residueMap (inVariable e i) =
      (MvPowerSeries.X i : MvPowerSeries σ F.residueField) ^
        Nat.card F.residueField := by
  have hX : PowerSeries.HasSubst
      (MvPowerSeries.X i : MvPowerSeries σ F.valuationSubring) :=
    PowerSeries.HasSubst.X i
  have hXbar : PowerSeries.HasSubst
      (MvPowerSeries.X i : MvPowerSeries σ F.residueField) :=
    PowerSeries.HasSubst.X i
  rw [inVariable, PowerSeries.map_subst hX e.toPowerSeries,
    e.map_residue_eq_frobenius, MvPowerSeries.map_X,
    PowerSeries.subst_pow hXbar, PowerSeries.subst_X hXbar]

/-- The reduced left side `e(H)` is `Hbar ^ q`. -/
theorem map_subst_lubinTateSeries
    (e : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L) :
    MvPowerSeries.map F.residueMap
        (PowerSeries.subst H e.toPowerSeries) =
      (MvPowerSeries.map F.residueMap H) ^
        Nat.card F.residueField := by
  have hmap : PowerSeries.HasSubst
      (MvPowerSeries.map F.residueMap H) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by
      simp [hH.constantCoeff_eq_zero])
  rw [PowerSeries.map_subst hH.hasSubst e.toPowerSeries,
    e.map_residue_eq_frobenius, PowerSeries.subst_pow hmap,
    PowerSeries.subst_X hmap]

/-- The reduced right side `H(ebar(X_i))` is the expansion
`Hbar(X_i ^ q)`. -/
theorem map_subst_inVariables
    (ebar : LubinTateSeries F π)
    (H : MvPowerSeries σ F.valuationSubring) :
    MvPowerSeries.map F.residueMap
        (MvPowerSeries.subst
          (fun i : σ ↦ inVariable ebar i) H) =
      MvPowerSeries.expand (Nat.card F.residueField)
        (Nat.ne_of_gt Nat.card_pos)
        (MvPowerSeries.map F.residueMap H) := by
  rw [MvPowerSeries.map_subst (inVariable_hasSubst ebar) H]
  simp_rw [map_inVariable]
  rw [MvPowerSeries.expand, MvPowerSeries.substAlgHom_apply]

/-- The same-uniformizer intertwining defect vanishes after reduction. -/
theorem map_defect_eq_zero
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L) :
    MvPowerSeries.map F.residueMap (defect e ebar H) = 0 := by
  rw [defect, map_sub, map_subst_lubinTateSeries e hH,
    map_subst_inVariables ebar H,
    mvPowerSeries_expand_natCard]
  exact sub_self _

/-- Every coefficient of the defect is divisible by the chosen
uniformizer. -/
theorem uniformizer_dvd_coeff_defect
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) :
    π ∣ MvPowerSeries.coeff d (defect e ebar H) := by
  apply uniformizer_dvd_of_residueMap_eq_zero hπ
  have hcoeff := congrArg (MvPowerSeries.coeff d)
    (map_defect_eq_zero e ebar hH)
  simpa using hcoeff

end SameUniformizer
end LubinTate

end
