/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.CompletedIterates
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveAction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LevelValuation
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Inverse
/-!
# Displacements of primitive Lubin--Tate points

For the primitive point at level `n + 1`, a unit whose first nontrivial
principal-unit layer is `k` displaces that point by an element of normalized
additive valuation `q ^ k`.

The analytic input is proved here rather than assumed.  A unit scalar
endomorphism is `X` times an invertible power series.  Likewise
`F(X, Y) - X` for the standard formal group is `Y` times an invertible
two-variable power series.  Consequently neither operation changes the
valuation of the topologically nilpotent input that it multiplies.
-/

@[expose] public section

noncomputable
section

open scoped Polynomial PowerSeries

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

section FormalFactors

private theorem coeff_subst_X_zero
    {R : Type*} [CommRing R]
    (f : MvPowerSeries (Fin 2) R) (d : Fin 2 →₀ ℕ)
    (hd : d 1 = 0) :
    PowerSeries.coeff (d 0)
        (MvPowerSeries.subst
          ![(PowerSeries.X : PowerSeries R), 0] f) =
      MvPowerSeries.coeff d f := by
  rw [PowerSeries.coeff, MvPowerSeries.coeff_subst,
    finsum_eq_single _ d]
  · simp [hd, PowerSeries.coeff_X_pow]
  · intro e hed
    by_cases he : e 1 = 0
    · have he0 : e 0 ≠ d 0 := by
        intro he0
        apply hed
        ext i
        fin_cases i
        · exact he0
        · exact he.trans hd.symm
      simp [he, PowerSeries.coeff_X_pow, he0.symm]
    · simp [he]
  · exact MvPowerSeries.HasSubst.X_zero

/-- The standard formal-group difference `F(X,Y) - X` is divisible by
`Y`. -/
private theorem standardLubinTateFormalGroup_rightDisplacement_dvd
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    (MvPowerSeries.X (1 : Fin 2) :
        MvPowerSeries (Fin 2) F.valuationSubring) ∣
      SameUniformizer.standardFormalGroupPowerSeries hπ -
        MvPowerSeries.X (0 : Fin 2) := by
  rw [MvPowerSeries.X_dvd_iff]
  intro d hd
  let D :=
    SameUniformizer.standardFormalGroupPowerSeries hπ -
      MvPowerSeries.X (0 : Fin 2)
  have hhas :
      MvPowerSeries.HasSubst
        (![(PowerSeries.X : PowerSeries F.valuationSubring), 0] :
          Fin 2 → PowerSeries F.valuationSubring) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro i
    fin_cases i
    · simpa only [Fin.zero_eta, Matrix.cons_val_zero,
        PowerSeries.X_apply] using
        (MvPowerSeries.constantCoeff_X
          (R := F.valuationSubring) ())
    · simp
  have hsubst :
      MvPowerSeries.subst
          ![(PowerSeries.X : PowerSeries F.valuationSubring), 0] D =
        0 := by
    dsimp only [D]
    rw [MvPowerSeries.subst_sub hhas]
    have hformal :
        MvPowerSeries.subst
            ![(PowerSeries.X : PowerSeries F.valuationSubring), 0]
            (SameUniformizer.standardFormalGroupPowerSeries hπ) =
          PowerSeries.X := by
      simpa only [PowerSeries.X_apply] using
        SameUniformizer.standardFormalGroupPowerSeries_subst_X_zero hπ
    rw [hformal, MvPowerSeries.subst_X hhas]
    exact sub_self _
  have hcoeff :=
    congrArg (PowerSeries.coeff (d 0)) hsubst
  rw [coeff_subst_X_zero D d hd] at hcoeff
  simpa [D] using hcoeff

/-- The quotient of `F(X,Y) - X` by `Y`. -/
private noncomputable def standardLubinTateFormalGroupRightDisplacementFactor
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    MvPowerSeries (Fin 2) F.valuationSubring :=
  Classical.choose
    (standardLubinTateFormalGroup_rightDisplacement_dvd hπ)

/-- Factorization of the ordinary displacement in the standard formal
group. -/
private theorem standardLubinTateFormalGroup_rightDisplacement_factor
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    SameUniformizer.standardFormalGroupPowerSeries hπ -
        MvPowerSeries.X (0 : Fin 2) =
      MvPowerSeries.X (1 : Fin 2) *
        standardLubinTateFormalGroupRightDisplacementFactor hπ :=
  Classical.choose_spec
    (standardLubinTateFormalGroup_rightDisplacement_dvd hπ)

/-- The formal-group displacement factor has constant coefficient one. -/
private theorem
    standardLubinTateFormalGroupRightDisplacementFactor_constantCoeff
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    MvPowerSeries.constantCoeff
        (standardLubinTateFormalGroupRightDisplacementFactor hπ) = 1 := by
  let H := standardLubinTateFormalGroupRightDisplacementFactor hπ
  have hfactor :=
    congrArg
      (MvPowerSeries.coeff
        (Finsupp.single (1 : Fin 2) 1))
      (standardLubinTateFormalGroup_rightDisplacement_factor hπ)
  have hleft :
      MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1)
          (SameUniformizer.standardFormalGroupPowerSeries hπ -
            MvPowerSeries.X (0 : Fin 2)) = 1 := by
    rw [map_sub,
      (SameUniformizer.standardFormalGroupPowerSeries_hasLinearTerm
        hπ).coeff_single]
    simp [MvPowerSeries.coeff_index_single_X]
  have hright :
      MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1)
          (MvPowerSeries.X (1 : Fin 2) * H) =
        MvPowerSeries.constantCoeff H := by
    rw [MvPowerSeries.X_def]
    simpa only [add_zero, one_mul,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using
      (MvPowerSeries.coeff_add_monomial_mul
        (m := Finsupp.single (1 : Fin 2) 1)
        (n := 0) H 1)
  rw [hleft, hright] at hfactor
  exact hfactor.symm

/-- The formal-group displacement factor is invertible. -/
private theorem standardLubinTateFormalGroupRightDisplacementFactor_isUnit
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    IsUnit (standardLubinTateFormalGroupRightDisplacementFactor hπ) := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff,
    standardLubinTateFormalGroupRightDisplacementFactor_constantCoeff]
  exact isUnit_one

/-- The factor left after removing `X` from the scalar endomorphism
`[a](X)`. -/
private noncomputable def standardLubinTateEndomorphismLinearFactor
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (a : F.valuationSubring) :
    PowerSeries F.valuationSubring :=
  PowerSeries.mk fun m =>
    PowerSeries.coeff (m + 1)
      (SameUniformizer.standardLubinTateEndomorphism hπ a)

/-- A standard scalar endomorphism is `X` times its linear factor. -/
private theorem standardLubinTateEndomorphism_eq_X_mul_linearFactor
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (a : F.valuationSubring) :
    SameUniformizer.standardLubinTateEndomorphism hπ a =
      PowerSeries.X *
        standardLubinTateEndomorphismLinearFactor hπ a := by
  have hsplit :=
    PowerSeries.eq_X_mul_shift_add_const
      (SameUniformizer.standardLubinTateEndomorphism hπ a)
  have hconstant :
      PowerSeries.constantCoeff
          (SameUniformizer.standardLubinTateEndomorphism hπ a) = 0 :=
    (SameUniformizer.standardLubinTateEndomorphism_hasLinearTerm
      hπ a).constantCoeff_eq_zero
  calc
    SameUniformizer.standardLubinTateEndomorphism hπ a =
        PowerSeries.X *
            standardLubinTateEndomorphismLinearFactor hπ a +
          PowerSeries.C
            (PowerSeries.constantCoeff
              (SameUniformizer.standardLubinTateEndomorphism hπ a)) := hsplit
    _ = PowerSeries.X *
          standardLubinTateEndomorphismLinearFactor hπ a := by
      rw [hconstant, map_zero, add_zero]

/-- The constant coefficient of the linear factor is the scalar. -/
private theorem standardLubinTateEndomorphismLinearFactor_constantCoeff
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (a : F.valuationSubring) :
    PowerSeries.constantCoeff
        (standardLubinTateEndomorphismLinearFactor hπ a) = a := by
  change
    PowerSeries.coeff 1
      (SameUniformizer.standardLubinTateEndomorphism hπ a) = a
  exact SameUniformizer.standardLubinTateEndomorphism_coeff_one hπ a

/-- The linear factor of a unit scalar endomorphism is invertible. -/
private theorem standardLubinTateEndomorphismLinearFactor_isUnit
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (a : F.valuationSubringˣ) :
    IsUnit
      (standardLubinTateEndomorphismLinearFactor hπ
        (a : F.valuationSubring)) := by
  rw [PowerSeries.isUnit_iff_constantCoeff,
    standardLubinTateEndomorphismLinearFactor_constantCoeff]
  exact a.isUnit

end FormalFactors

section AnalyticValuation

private noncomputable local instance
    standardLubinTatePrimitiveDisplacementCoefficientUniformSpace :
    UniformSpace F.valuationSubring :=
  ⊥

private noncomputable local instance
    standardLubinTatePrimitiveDisplacementTargetWithIdeal
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    WithIdeal
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring where
  i := (standardLubinTateLevelCompleteDVF hπ n).maximalIdeal

private noncomputable local instance
    standardLubinTatePrimitiveDisplacementTargetCompleteSpace
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    CompleteSpace
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring := by
  let target := standardLubinTateLevelCompleteDVF hπ n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).1

private noncomputable local instance
    standardLubinTatePrimitiveDisplacementTargetT2Space
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    T2Space
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring := by
  let target := standardLubinTateLevelCompleteDVF hπ n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).2

private noncomputable local instance
    standardLubinTatePrimitiveDisplacementAlgebra
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    Algebra F.valuationSubring
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring :=
  (standardLubinTateLevelCoefficientHom hπ n).toAlgebra

private theorem hasEval_fin_two
    {R : Type*} [CommRing R] [TopologicalSpace R]
    {x y : R} (hx : PowerSeries.HasEval x)
    (hy : PowerSeries.HasEval y) :
    MvPowerSeries.HasEval (![x, y] : Fin 2 → R) := by
  constructor
  · intro i
    fin_cases i
    · exact hx
    · exact hy
  · simp [Filter.cofinite_eq_bot]

private theorem
    standardLubinTateEndomorphismEvalAt_congr_point_forPrimitiveDisplacement
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (x y : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
    (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
    (hxy : x = y) (a : F.valuationSubring) :
    standardLubinTateEndomorphismEvalAt hπ n x hx a =
      standardLubinTateEndomorphismEvalAt hπ n y hy a := by
  subst y
  rfl

/-- Ordinary subtraction after standard formal-group addition has the same
additive valuation as the added topologically nilpotent point. -/
theorem standardLubinTateFormalAdd_sub_left_addVal
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (x z :
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
    (hx : PowerSeries.HasEval x) (hz : PowerSeries.HasEval z) :
    IsDiscreteValuationRing.addVal
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
        (standardLubinTateFormalAdd hπ n x z - x) =
      IsDiscreteValuationRing.addVal
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring z := by
  let hvec : MvPowerSeries.HasEval (![x, z] : Fin 2 →
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring) :=
    hasEval_fin_two hx hz
  let ev :
      MvPowerSeries (Fin 2) F.valuationSubring →+*
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring :=
    MvPowerSeries.eval₂Hom
      (φ := standardLubinTateLevelCoefficientHom hπ n)
      continuous_of_discreteTopology hvec
  let e :=
    ev (standardLubinTateFormalGroupRightDisplacementFactor hπ)
  have he : IsUnit e :=
    (standardLubinTateFormalGroupRightDisplacementFactor_isUnit hπ).map ev
  have hfactor := congrArg ev
    (standardLubinTateFormalGroup_rightDisplacement_factor hπ)
  have hdisplacement :
      standardLubinTateFormalAdd hπ n x z - x = z * e := by
    calc
      standardLubinTateFormalAdd hπ n x z - x =
          ev (SameUniformizer.standardFormalGroupPowerSeries hπ) -
            ev (MvPowerSeries.X (0 : Fin 2)) := by
        simp [standardLubinTateFormalAdd, ev,
          MvPowerSeries.coe_eval₂Hom]
      _ =
          ev
            (SameUniformizer.standardFormalGroupPowerSeries hπ -
              MvPowerSeries.X (0 : Fin 2)) :=
        (map_sub ev _ _).symm
      _ =
          ev
            (MvPowerSeries.X (1 : Fin 2) *
              standardLubinTateFormalGroupRightDisplacementFactor hπ) :=
        hfactor
      _ =
          ev (MvPowerSeries.X (1 : Fin 2)) *
            ev (standardLubinTateFormalGroupRightDisplacementFactor hπ) :=
        map_mul ev _ _
      _ = z * e := by
        simp [ev, e, MvPowerSeries.coe_eval₂Hom]
  rw [hdisplacement, IsDiscreteValuationRing.addVal_mul,
    (IsDiscreteValuationRing.addVal_eq_zero_iff).2 he, add_zero]

/-- A unit scalar endomorphism preserves normalized additive valuation on
every topologically nilpotent point of a finite level. -/
theorem standardLubinTateEndomorphismEvalAt_unit_addVal
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (x : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
    (hx : PowerSeries.HasEval x) (a : F.valuationSubringˣ) :
    IsDiscreteValuationRing.addVal
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
        (standardLubinTateEndomorphismEvalAt hπ n x hx
          (a : F.valuationSubring)) =
      IsDiscreteValuationRing.addVal
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring x := by
  let ev :=
    standardLubinTateLevelPowerSeriesEval hπ n x hx
  let e :=
    ev (standardLubinTateEndomorphismLinearFactor hπ
      (a : F.valuationSubring))
  have he : IsUnit e :=
    (standardLubinTateEndomorphismLinearFactor_isUnit hπ a).map ev
  have hfactor := congrArg ev
    (standardLubinTateEndomorphism_eq_X_mul_linearFactor
      hπ (a : F.valuationSubring))
  have heval :
      standardLubinTateEndomorphismEvalAt hπ n x hx
          (a : F.valuationSubring) =
        x * e := by
    simpa [standardLubinTateEndomorphismEvalAt, ev, e] using hfactor
  rw [heval, IsDiscreteValuationRing.addVal_mul,
    (IsDiscreteValuationRing.addVal_eq_zero_iff).2 he, add_zero]

/-- The analytic value of `[π^k]` is the evaluated standard polynomial
iterate. -/
theorem standardLubinTateEndomorphismValue_uniformizer_pow
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n k : ℕ) :
    standardLubinTateEndomorphismValue hπ n (π ^ k) =
      standardLubinTatePrimitivePointIterateInteger hπ n k := by
  exact
    standardLubinTateEndomorphismEvalAt_uniformizer_pow hπ n
      (standardLubinTatePrimitivePointInteger hπ n)
      (standardLubinTatePrimitivePointInteger_hasEval hπ n) k

/-- Every evaluated standard iterate before the annihilating level is
topologically nilpotent. -/
theorem standardLubinTatePrimitivePointIterateInteger_hasEval
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n k : ℕ) :
    PowerSeries.HasEval
      (standardLubinTatePrimitivePointIterateInteger hπ n k) := by
  rw [← standardLubinTateEndomorphismValue_uniformizer_pow hπ n k]
  exact standardLubinTateEndomorphismValue_hasEval hπ n (π ^ k)

/-- An element in the exact `k`th principal-unit layer is a unit times
`π^k`. -/
private theorem exists_unit_mul_uniformizer_pow_of_exactDepth
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (a : F.valuationSubringˣ) (k : ℕ)
    (ha :
      a ∈ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF k)
    (hnot :
      a ∉ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (k + 1)) :
    ∃ c : F.valuationSubringˣ,
      (a : F.valuationSubring) - 1 =
        (c : F.valuationSubring) * π ^ k := by
  have hamem :
      (a : F.valuationSubring) - 1 ∈
        F.toCompleteDVF.maximalIdeal ^ k :=
    (CompleteDVF.higherPrincipalUnitGroup.mem_iff
      F.toCompleteDVF k a).mp ha
  have hanot :
      (a : F.valuationSubring) - 1 ∉
        F.toCompleteDVF.maximalIdeal ^ (k + 1) := by
    intro h
    exact hnot
      ((CompleteDVF.higherPrincipalUnitGroup.mem_iff
        F.toCompleteDVF (k + 1) a).mpr h)
  have hdiv :
      π ^ k ∣ (a : F.valuationSubring) - 1 :=
    (F.toCompleteDVF.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd
      hπ k).mp hamem
  rcases hdiv with ⟨c, hc⟩
  have hcnot : c ∉ F.toCompleteDVF.maximalIdeal := by
    intro hcmem
    have hdeep :
        c * π ^ k ∈ F.toCompleteDVF.maximalIdeal ^ (k + 1) :=
      (F.toCompleteDVF.toDVF
        |>.mul_uniformizer_pow_mem_maximalIdeal_pow_succ_iff
          hπ k c).mpr hcmem
    apply hanot
    rw [hc, mul_comm]
    exact hdeep
  have hcunit : IsUnit c :=
    (IsLocalRing.notMem_maximalIdeal).mp hcnot
  rcases hcunit with ⟨cunit, rfl⟩
  refine ⟨cunit, ?_⟩
  simpa [mul_comm] using hc

/-- Exact principal-unit depth controls the valuation of `[a - 1]` at the
primitive point. -/
theorem standardLubinTateEndomorphismValue_sub_one_addVal_of_exactDepth
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : F.valuationSubringˣ) (k : ℕ)
    (ha :
      a ∈ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF k)
    (hnot :
      a ∉ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (k + 1))
    (hk : k ≤ n) :
    IsDiscreteValuationRing.addVal
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
        (standardLubinTateEndomorphismValue hπ n
          ((a : F.valuationSubring) - 1)) =
      (Nat.card F.residueField ^ k : ℕ) := by
  obtain ⟨c, hc⟩ :=
    exists_unit_mul_uniformizer_pow_of_exactDepth hπ a k ha hnot
  calc
    IsDiscreteValuationRing.addVal
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
        (standardLubinTateEndomorphismValue hπ n
          ((a : F.valuationSubring) - 1)) =
      IsDiscreteValuationRing.addVal
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
        (standardLubinTateEndomorphismEvalAt hπ n
          (standardLubinTatePrimitivePointIterateInteger hπ n k)
          (standardLubinTatePrimitivePointIterateInteger_hasEval hπ n k)
          (c : F.valuationSubring)) := by
            rw [hc, standardLubinTateEndomorphismValue_mul]
            apply congrArg
              (IsDiscreteValuationRing.addVal
                (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
            exact
              standardLubinTateEndomorphismEvalAt_congr_point_forPrimitiveDisplacement
                hπ n
                (standardLubinTateEndomorphismValue hπ n (π ^ k))
                (standardLubinTatePrimitivePointIterateInteger hπ n k)
                (standardLubinTateEndomorphismValue_hasEval hπ n (π ^ k))
                (standardLubinTatePrimitivePointIterateInteger_hasEval hπ n k)
                (standardLubinTateEndomorphismValue_uniformizer_pow hπ n k)
                (c : F.valuationSubring)
    _ =
      IsDiscreteValuationRing.addVal
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
        (standardLubinTatePrimitivePointIterateInteger hπ n k) :=
      standardLubinTateEndomorphismEvalAt_unit_addVal hπ n
        (standardLubinTatePrimitivePointIterateInteger hπ n k)
        (standardLubinTatePrimitivePointIterateInteger_hasEval hπ n k) c
    _ = (Nat.card F.residueField ^ k : ℕ) :=
      standardLubinTatePrimitivePointIterateInteger_addVal hπ n k hk

/-- If a unit first differs from `1` in principal-unit depth `k`, its
ordinary displacement of the primitive point has valuation exactly
`q^k`. -/
theorem
    standardLubinTatePrimitivePointIntegerAction_sub_self_addVal_of_exactDepth
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : F.valuationSubringˣ) (k : ℕ)
    (ha :
      a ∈ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF k)
    (hnot :
      a ∉ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (k + 1))
    (hk : k ≤ n) :
    IsDiscreteValuationRing.addVal
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
        (standardLubinTatePrimitivePointIntegerAction hπ n a -
          standardLubinTatePrimitivePointInteger hπ n) =
      (Nat.card F.residueField ^ k : ℕ) := by
  let lambda := standardLubinTatePrimitivePointInteger hπ n
  let z :=
    standardLubinTateEndomorphismValue hπ n
      ((a : F.valuationSubring) - 1)
  have haction :
      standardLubinTatePrimitivePointIntegerAction hπ n a =
        standardLubinTateFormalAdd hπ n lambda z := by
    change
      standardLubinTateEndomorphismValue hπ n
          (a : F.valuationSubring) =
        standardLubinTateFormalAdd hπ n lambda z
    calc
      standardLubinTateEndomorphismValue hπ n
          (a : F.valuationSubring) =
        standardLubinTateEndomorphismValue hπ n
          (1 + ((a : F.valuationSubring) - 1)) := by
            congr 1
            ring
      _ =
        standardLubinTateFormalAdd hπ n
          (standardLubinTateEndomorphismValue hπ n 1)
          (standardLubinTateEndomorphismValue hπ n
            ((a : F.valuationSubring) - 1)) :=
        standardLubinTateEndomorphismValue_add hπ n 1
          ((a : F.valuationSubring) - 1)
      _ = standardLubinTateFormalAdd hπ n lambda z := by
        rw [standardLubinTateEndomorphismValue_one]
  rw [haction]
  calc
    IsDiscreteValuationRing.addVal
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
        (standardLubinTateFormalAdd hπ n lambda z - lambda) =
      IsDiscreteValuationRing.addVal
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring z :=
      standardLubinTateFormalAdd_sub_left_addVal hπ n lambda z
        (standardLubinTatePrimitivePointInteger_hasEval hπ n)
        (standardLubinTateEndomorphismValue_hasEval hπ n
          ((a : F.valuationSubring) - 1))
    _ = (Nat.card F.residueField ^ k : ℕ) :=
      standardLubinTateEndomorphismValue_sub_one_addVal_of_exactDepth
        hπ n a k ha hnot hk

/-- Principal-unit membership is antitone in the depth index. -/
private theorem higherPrincipalUnitGroup_mem_of_le
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (a : F.valuationSubringˣ) {k r : ℕ} (hkr : k ≤ r)
    (ha :
      a ∈ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF r) :
    a ∈ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF k := by
  rw [CompleteDVF.higherPrincipalUnitGroup.mem_iff] at ha ⊢
  rw [F.toCompleteDVF.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd
    hπ r] at ha
  rw [F.toCompleteDVF.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd
    hπ k]
  exact (pow_dvd_pow π hkr).trans ha

/-- If `a - 1` is a unit times `π^r`, then membership in `U^k` is
equivalent to `k ≤ r`. -/
private theorem
    mem_higherPrincipalUnitGroup_iff_le_of_sub_eq_unit_mul_uniformizer_pow
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (a c : F.valuationSubringˣ) (r k : ℕ)
    (hsub :
      (a : F.valuationSubring) - 1 =
        (c : F.valuationSubring) * π ^ r) :
    a ∈ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF k ↔
      k ≤ r := by
  rw [CompleteDVF.higherPrincipalUnitGroup.mem_iff,
    F.toCompleteDVF.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd hπ k]
  constructor
  · intro hdiv
    by_contra hkr
    have hrk : r + 1 ≤ k := by omega
    have hdeepDiv :
        π ^ (r + 1) ∣ (a : F.valuationSubring) - 1 :=
      (pow_dvd_pow π hrk).trans hdiv
    have hdeep :
        (a : F.valuationSubring) - 1 ∈
          F.toCompleteDVF.maximalIdeal ^ (r + 1) :=
      (F.toCompleteDVF.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd
        hπ (r + 1)).mpr hdeepDiv
    have hcmem : (c : F.valuationSubring) ∈
        F.toCompleteDVF.maximalIdeal := by
      exact
        (F.toCompleteDVF.toDVF
          |>.mul_uniformizer_pow_mem_maximalIdeal_pow_succ_iff
            hπ r (c : F.valuationSubring)).mp (by
          simpa [hsub] using hdeep)
    exact
      ((IsLocalRing.notMem_maximalIdeal).mpr c.isUnit) hcmem
  · intro hkr
    rcases pow_dvd_pow π hkr with ⟨b, hb⟩
    refine ⟨(c : F.valuationSubring) * b, ?_⟩
    rw [hsub, hb]
    ring

/-- At a standard finite level, the valuation threshold `q^k` detects
exactly the `k`th principal-unit subgroup.  The statement includes the
identity action, whose displacement has infinite additive valuation. -/
theorem
    standardLubinTatePrimitivePointIntegerAction_sub_self_addVal_ge_iff_mem
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : F.valuationSubringˣ) (k : ℕ)
    (hk : k ≤ n + 1) :
    ((Nat.card F.residueField ^ k : ℕ) : ℕ∞) ≤
        IsDiscreteValuationRing.addVal
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
          (standardLubinTatePrimitivePointIntegerAction hπ n a -
            standardLubinTatePrimitivePointInteger hπ n) ↔
      a ∈ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF k := by
  by_cases hdeep :
      a ∈ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)
  · have hfix :=
      (standardLubinTatePrimitivePointIntegerAction_eq_self_iff_mem_higherPrincipalUnitGroup
        hπ n a).2 hdeep
    have hmem :=
      higherPrincipalUnitGroup_mem_of_le hπ a hk hdeep
    constructor
    · intro
      exact hmem
    · intro
      rw [hfix, sub_self]
      simp
  · have hsubne :
        (a : F.valuationSubring) - 1 ≠ 0 := by
      intro hzero
      apply hdeep
      rw [CompleteDVF.higherPrincipalUnitGroup.mem_iff]
      simp [hzero]
    have hπirr : Irreducible π :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2
        (F.toCompleteDVF.maximalIdeal_eq_span_uniformizer hπ)
    obtain ⟨r, c, hsub⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        hsubne hπirr
    have hr : r ≤ n := by
      by_contra hrn
      apply hdeep
      exact
        (mem_higherPrincipalUnitGroup_iff_le_of_sub_eq_unit_mul_uniformizer_pow
          hπ a c r (n + 1) hsub).2 (by omega)
    have hrmem :
        a ∈ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF r :=
      (mem_higherPrincipalUnitGroup_iff_le_of_sub_eq_unit_mul_uniformizer_pow
        hπ a c r r hsub).2 le_rfl
    have hrnot :
        a ∉ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (r + 1) := by
      rw [
        mem_higherPrincipalUnitGroup_iff_le_of_sub_eq_unit_mul_uniformizer_pow
          hπ a c r (r + 1) hsub]
      omega
    have hval :=
      standardLubinTatePrimitivePointIntegerAction_sub_self_addVal_of_exactDepth
        hπ n a r hrmem hrnot hr
    rw [hval,
      mem_higherPrincipalUnitGroup_iff_le_of_sub_eq_unit_mul_uniformizer_pow
        hπ a c r k hsub]
    have hqone : 1 < Nat.card F.residueField :=
      Finite.one_lt_card
    constructor
    · intro hpow
      by_contra hkr
      have hrk : r < k := Nat.lt_of_not_ge hkr
      have hltNat :
          Nat.card F.residueField ^ r <
            Nat.card F.residueField ^ k :=
        Nat.pow_lt_pow_right hqone hrk
      have hlt :
          (Nat.card F.residueField ^ r : ℕ∞) <
            (Nat.card F.residueField ^ k : ℕ) := by
        exact_mod_cast hltNat
      exact (not_lt_of_ge hpow) hlt
    · intro hkr
      have hpowNat :
          Nat.card F.residueField ^ k ≤
            Nat.card F.residueField ^ r :=
        Nat.pow_le_pow_right (Nat.zero_lt_one.trans hqone) hkr
      exact_mod_cast hpowNat

/-- On the interval
`q^(k-1) - 1 ≤ r ≤ q^k - 1`, the lower displacement bound `r + 1`
detects the `k`th principal-unit subgroup. -/
theorem
    standardLubinTatePrimitivePointIntegerAction_sub_self_addVal_ge_iff_mem_of_pow_interval
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : F.valuationSubringˣ) (k r : ℕ)
    (hkpos : 1 ≤ k) (hk : k ≤ n + 1)
    (hlower : Nat.card F.residueField ^ (k - 1) ≤ r)
    (hupper : r < Nat.card F.residueField ^ k) :
    (((r + 1 : ℕ) : ℕ∞) ≤
        IsDiscreteValuationRing.addVal
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
          (standardLubinTatePrimitivePointIntegerAction hπ n a -
            standardLubinTatePrimitivePointInteger hπ n)) ↔
      a ∈ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF k := by
  constructor
  · intro hdisplacement
    by_contra hnot
    have hnotDeep :
        a ∉ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF
          (n + 1) := by
      intro hdeep
      exact hnot
        (higherPrincipalUnitGroup_mem_of_le hπ a hk hdeep)
    have hsubne :
        (a : F.valuationSubring) - 1 ≠ 0 := by
      intro hzero
      apply hnotDeep
      rw [CompleteDVF.higherPrincipalUnitGroup.mem_iff]
      simp [hzero]
    have hπirr : Irreducible π :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2
        (F.toCompleteDVF.maximalIdeal_eq_span_uniformizer hπ)
    obtain ⟨j, c, hsub⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        hsubne hπirr
    have hj : j ≤ n := by
      by_contra hjn
      apply hnotDeep
      exact
        (mem_higherPrincipalUnitGroup_iff_le_of_sub_eq_unit_mul_uniformizer_pow
          hπ a c j (n + 1) hsub).2 (by omega)
    have hjmem :
        a ∈ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF j :=
      (mem_higherPrincipalUnitGroup_iff_le_of_sub_eq_unit_mul_uniformizer_pow
        hπ a c j j hsub).2 le_rfl
    have hjnot :
        a ∉ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (j + 1) := by
      rw [
        mem_higherPrincipalUnitGroup_iff_le_of_sub_eq_unit_mul_uniformizer_pow
          hπ a c j (j + 1) hsub]
      omega
    have hjk : j < k := by
      by_contra hjk
      apply hnot
      exact
        (mem_higherPrincipalUnitGroup_iff_le_of_sub_eq_unit_mul_uniformizer_pow
          hπ a c j k hsub).2 (by omega)
    have hval :=
      standardLubinTatePrimitivePointIntegerAction_sub_self_addVal_of_exactDepth
        hπ n a j hjmem hjnot hj
    rw [hval] at hdisplacement
    have hdisplacementNat :
        r + 1 ≤ Nat.card F.residueField ^ j := by
      exact_mod_cast hdisplacement
    have hqpos : 0 < Nat.card F.residueField :=
      Nat.zero_lt_one.trans Finite.one_lt_card
    have hjpred : j ≤ k - 1 := by omega
    have hjpow :
        Nat.card F.residueField ^ j ≤
          Nat.card F.residueField ^ (k - 1) :=
      Nat.pow_le_pow_right hqpos hjpred
    omega
  · intro hmem
    have hthreshold :=
      (standardLubinTatePrimitivePointIntegerAction_sub_self_addVal_ge_iff_mem
        hπ n a k hk).2 hmem
    have hrqNat :
        r + 1 ≤ Nat.card F.residueField ^ k :=
      Nat.succ_le_of_lt hupper
    have hrq :
        ((r + 1 : ℕ) : ℕ∞) ≤
          (Nat.card F.residueField ^ k : ℕ) := by
      exact_mod_cast hrqNat
    exact hrq.trans hthreshold

section ParameterDisplacement

private noncomputable local instance
    standardLubinTateLevelField_finiteDimensional_forPrimitiveDisplacement
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    FiniteDimensional K (standardLubinTateLevelField hπ n) :=
  standardLubinTateLevelField_finiteDimensional hπ n

private noncomputable local instance
    standardLubinTateLevelField_isGalois_forPrimitiveDisplacement
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    IsGalois K (standardLubinTateLevelField hπ n) :=
  standardLubinTateLevelField_isGalois hπ n

/-- The valuation-ring action of the automorphism attached to a finite unit
parameter agrees with the analytic action of its chosen representative on
the primitive point. -/
theorem standardLubinTateUnitParameterToGal_apply_primitivePointInteger
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : standardLubinTateUnitParameter F n) :
    valuationSubringAutOfUniqueExtension
        (standardLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
          hπ n)
        (standardLubinTateUnitParameterToGal F hπ n a)
        (standardLubinTatePrimitivePointInteger hπ n) =
      standardLubinTatePrimitivePointIntegerAction hπ n
        (standardLubinTateUnitParameterChosenRepresentative F n a) := by
  apply Subtype.ext
  change
    standardLubinTateUnitParameterToGal F hπ n a
        (standardLubinTateLevelGenerator hπ n) =
      (standardLubinTatePrimitivePointIntegerAction hπ n
          (standardLubinTateUnitParameterChosenRepresentative F n a) :
        standardLubinTateLevelField hπ n)
  change
    standardLubinTateUnitParameterAlgEquiv F hπ n a
        (standardLubinTateLevelPowerBasis hπ n).gen =
      standardLubinTateUnitParameterLevelRoot F hπ n a
  exact standardLubinTateUnitParameterAlgEquiv_apply_gen F hπ n a

/-- Exact depth of a chosen finite-parameter representative computes the
displacement of the corresponding Galois automorphism. -/
theorem
    standardLubinTateUnitParameterToGal_displacement_addVal_of_chosenRepresentative_exactDepth
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : standardLubinTateUnitParameter F n) (k : ℕ)
    (ha :
      standardLubinTateUnitParameterChosenRepresentative F n a ∈
        CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF k)
    (hnot :
      standardLubinTateUnitParameterChosenRepresentative F n a ∉
        CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (k + 1))
    (hk : k ≤ n) :
    IsDiscreteValuationRing.addVal
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
        (valuationSubringAutOfUniqueExtension
            (standardLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
              hπ n)
            (standardLubinTateUnitParameterToGal F hπ n a)
            (standardLubinTatePrimitivePointInteger hπ n) -
          standardLubinTatePrimitivePointInteger hπ n) =
      (Nat.card F.residueField ^ k : ℕ) := by
  rw [standardLubinTateUnitParameterToGal_apply_primitivePointInteger]
  exact
    standardLubinTatePrimitivePointIntegerAction_sub_self_addVal_of_exactDepth
      hπ n
      (standardLubinTateUnitParameterChosenRepresentative F n a)
      k ha hnot hk

/-- The `q^k` displacement threshold for a finite-parameter automorphism is
equivalent to its chosen representative belonging to `U^k`. -/
theorem
    standardLubinTateUnitParameterToGal_displacement_addVal_ge_iff_chosenRepresentative_mem
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : standardLubinTateUnitParameter F n) (k : ℕ)
    (hk : k ≤ n + 1) :
    ((Nat.card F.residueField ^ k : ℕ) : ℕ∞) ≤
        IsDiscreteValuationRing.addVal
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
          (valuationSubringAutOfUniqueExtension
              (standardLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
                hπ n)
              (standardLubinTateUnitParameterToGal F hπ n a)
              (standardLubinTatePrimitivePointInteger hπ n) -
            standardLubinTatePrimitivePointInteger hπ n) ↔
      standardLubinTateUnitParameterChosenRepresentative F n a ∈
        CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF k := by
  rw [standardLubinTateUnitParameterToGal_apply_primitivePointInteger]
  exact
    standardLubinTatePrimitivePointIntegerAction_sub_self_addVal_ge_iff_mem
      hπ n
      (standardLubinTateUnitParameterChosenRepresentative F n a) k hk

/-- The power-interval form of the finite-parameter displacement criterion,
stated using its chosen representative. -/
theorem
    unitParameterToGal_displacement_addVal_ge_iff_representative_mem_of_pow_interval
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : standardLubinTateUnitParameter F n) (k r : ℕ)
    (hkpos : 1 ≤ k) (hk : k ≤ n + 1)
    (hlower : Nat.card F.residueField ^ (k - 1) ≤ r)
    (hupper : r < Nat.card F.residueField ^ k) :
    (((r + 1 : ℕ) : ℕ∞) ≤
        IsDiscreteValuationRing.addVal
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
          (valuationSubringAutOfUniqueExtension
              (standardLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
                hπ n)
              (standardLubinTateUnitParameterToGal F hπ n a)
              (standardLubinTatePrimitivePointInteger hπ n) -
            standardLubinTatePrimitivePointInteger hπ n)) ↔
      standardLubinTateUnitParameterChosenRepresentative F n a ∈
        CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF k := by
  rw [standardLubinTateUnitParameterToGal_apply_primitivePointInteger]
  exact
    standardLubinTatePrimitivePointIntegerAction_sub_self_addVal_ge_iff_mem_of_pow_interval
      hπ n
      (standardLubinTateUnitParameterChosenRepresentative F n a)
      k r hkpos hk hlower hupper

/-- Every nontrivial displacement of the primitive point by a level Galois
automorphism has additive valuation at most `q ^ n`.

Surjectivity of the finite unit-parameter action supplies a representative.
If that representative fixed the point, it would lie in `U^(n+1)`.
Otherwise its first nontrivial depth is some `k ≤ n`, where the exact
displacement formula is `q^k`. -/
theorem standardLubinTateGal_displacement_addVal_le_of_ne
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (σ : Gal(standardLubinTateLevelField hπ n/K))
    (hne :
      valuationSubringAutOfUniqueExtension
          (standardLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
            hπ n)
          σ (standardLubinTatePrimitivePointInteger hπ n) ≠
        standardLubinTatePrimitivePointInteger hπ n) :
    IsDiscreteValuationRing.addVal
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
        (valuationSubringAutOfUniqueExtension
            (standardLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
              hπ n)
            σ (standardLubinTatePrimitivePointInteger hπ n) -
          standardLubinTatePrimitivePointInteger hπ n) ≤
      ((Nat.card F.residueField ^ n : ℕ) : ℕ∞) := by
  obtain ⟨a, rfl⟩ :=
    standardLubinTateUnitParameterToGal_surjective F hπ n σ
  let representative :=
    standardLubinTateUnitParameterChosenRepresentative F n a
  have hnotDeep :
      representative ∉
        CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1) := by
    intro hdeep
    apply hne
    rw [standardLubinTateUnitParameterToGal_apply_primitivePointInteger]
    exact
      (standardLubinTatePrimitivePointIntegerAction_eq_self_iff_mem_higherPrincipalUnitGroup
        hπ n representative).2 hdeep
  have hsubne :
      (representative : F.valuationSubring) - 1 ≠ 0 := by
    intro hzero
    apply hnotDeep
    rw [CompleteDVF.higherPrincipalUnitGroup.mem_iff]
    simp [hzero]
  have hπirr : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2
      (F.toCompleteDVF.maximalIdeal_eq_span_uniformizer hπ)
  obtain ⟨k, c, hsub⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      hsubne hπirr
  have hk : k ≤ n := by
    by_contra hkn
    apply hnotDeep
    exact
      (mem_higherPrincipalUnitGroup_iff_le_of_sub_eq_unit_mul_uniformizer_pow
        hπ representative c k (n + 1) hsub).2 (by omega)
  have hkmem :
      representative ∈
        CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF k :=
    (mem_higherPrincipalUnitGroup_iff_le_of_sub_eq_unit_mul_uniformizer_pow
      hπ representative c k k hsub).2 le_rfl
  have hknot :
      representative ∉
        CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (k + 1) := by
    rw [
      mem_higherPrincipalUnitGroup_iff_le_of_sub_eq_unit_mul_uniformizer_pow
        hπ representative c k (k + 1) hsub]
    omega
  have hval :=
    standardLubinTateUnitParameterToGal_displacement_addVal_of_chosenRepresentative_exactDepth
      F hπ n a k hkmem hknot hk
  rw [hval]
  exact_mod_cast
    Nat.pow_le_pow_right
      (Nat.zero_lt_one.trans Finite.one_lt_card) hk

end ParameterDisplacement

end AnalyticValuation

end LubinTate

end
