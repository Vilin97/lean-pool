/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.CompletedEvaluation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.ResidueQuotient
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.TeichmullerDecomposition
/-!
# The standard Lubin--Tate action on primitive division points

The formal scalar endomorphism `[a]` is in general an infinite power
series.  It is therefore evaluated on the primitive point only after that
point has been placed in the complete integral closure constructed in
`PrimitiveUniformizer`.  Unit scalars preserve the exact torsion level, so
their analytic values are again roots of the primitive division
polynomial.

The action is faithful precisely modulo the higher principal-unit subgroup
`U^(n + 1)`.  This is the finite-level congruence needed to descend the
action from valuation-ring units to the standard finite unit parameters.
-/

@[expose] public section

noncomputable section

open scoped Polynomial PowerSeries

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open ValuationTheory.DiscreteValuationField

variable {K : Type u} [Field K]

namespace SameUniformizer

variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

/-- The standard Lubin--Tate series itself has the prescribed linear term
`π X`. -/
private theorem standardLubinTateSeries_hasLinearTerm
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    HasLinearTerm (standardLubinTateSeries hπ).toPowerSeries
      (fun _ : Unit => π) := by
  have hlinear :
      (standardLubinTateSeries hπ).toPowerSeries -
          linearForm (fun _ : Unit => π) =
        (PowerSeries.X : PowerSeries F.valuationSubring) ^
          Nat.card F.residueField := by
    simp only [LubinTateSeries.standardLubinTateSeries_toPowerSeries,
      standardLubinTatePowerSeries, linearForm, Finset.univ_unique, PUnit.default_eq_unit,
      Finset.sum_singleton]
    rw [PowerSeries.C_apply, PowerSeries.X_apply]
    ring
  rw [HasLinearTerm, hlinear, ← PowerSeries.order_eq_order,
    PowerSeries.order_X_pow]
  exact_mod_cast (Finite.one_lt_card : 1 < Nat.card F.residueField)

/-- The scalar endomorphism attached to the uniformizer is the defining
standard Lubin--Tate series. -/
theorem standardLubinTateEndomorphism_uniformizer
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    standardLubinTateEndomorphism hπ π =
      (standardLubinTateSeries hπ).toPowerSeries := by
  apply
    eq_of_hasLinearTerm_of_intertwines hπ
      (standardLubinTateSeries hπ) (standardLubinTateSeries hπ)
      (fun _ : Unit => π)
      (standardLubinTateEndomorphism_hasLinearTerm hπ π)
      (standardLubinTateEndomorphism_intertwines hπ π)
      (standardLubinTateSeries_hasLinearTerm hπ)
  rw [Intertwines]
  change
    MvPowerSeries.subst
        (fun _ : Unit =>
          (standardLubinTateSeries hπ).toPowerSeries)
        (standardLubinTateSeries hπ).toPowerSeries =
      MvPowerSeries.subst
        (fun i : Unit =>
          inVariable (standardLubinTateSeries hπ) i)
        (standardLubinTateSeries hπ).toPowerSeries
  congr 1
  funext i
  cases i
  exact
    (PowerSeries.X_subst
      (standardLubinTateSeries hπ).toPowerSeries).symm

end SameUniformizer

section AnalyticAction

variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

private noncomputable local instance
    standardLubinTatePrimitiveActionCoefficientUniformSpace :
    UniformSpace F.valuationSubring :=
  ⊥

private noncomputable local instance
    standardLubinTatePrimitiveActionTargetWithIdeal
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    WithIdeal
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring where
  i := (standardLubinTateLevelCompleteDVF hπ n).maximalIdeal

private noncomputable local instance
    standardLubinTatePrimitiveActionTargetCompleteSpace
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    CompleteSpace
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring := by
  let target := standardLubinTateLevelCompleteDVF hπ n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).1

private noncomputable local instance
    standardLubinTatePrimitiveActionTargetT2Space
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    T2Space
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring := by
  let target := standardLubinTateLevelCompleteDVF hπ n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).2

private noncomputable local instance
    standardLubinTatePrimitiveActionAlgebra
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    Algebra F.valuationSubring
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring :=
  (standardLubinTateLevelCoefficientHom hπ n).toAlgebra

/-- Analytic addition in the standard formal group on the integer ring of a
finite level. -/
noncomputable def standardLubinTateFormalAdd
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (x y :
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring) :
    (standardLubinTateLevelCompleteDVF hπ n).valuationSubring :=
  MvPowerSeries.eval₂
    (standardLubinTateLevelCoefficientHom hπ n) ![x, y]
    (SameUniformizer.standardFormalGroupPowerSeries hπ)

/-- Analytic evaluation of scalar addition is addition in the standard
formal group. -/
theorem standardLubinTateEndomorphismEvalAt_add
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (x : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
    (hx : PowerSeries.HasEval x) (a b : F.valuationSubring) :
    standardLubinTateEndomorphismEvalAt hπ n x hx (a + b) =
      standardLubinTateFormalAdd hπ n
        (standardLubinTateEndomorphismEvalAt hπ n x hx a)
        (standardLubinTateEndomorphismEvalAt hπ n x hx b) := by
  let ea := SameUniformizer.standardLubinTateEndomorphism hπ a
  let eb := SameUniformizer.standardLubinTateEndomorphism hπ b
  have hea0 : PowerSeries.constantCoeff ea = 0 :=
    (SameUniformizer.standardLubinTateEndomorphism_hasLinearTerm
      hπ a).constantCoeff_eq_zero
  have heb0 : PowerSeries.constantCoeff eb = 0 :=
    (SameUniformizer.standardLubinTateEndomorphism_hasLinearTerm
      hπ b).constantCoeff_eq_zero
  have hab :
      MvPowerSeries.HasSubst (![ea, eb] :
        Fin 2 → PowerSeries F.valuationSubring) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero
      (fun i => by
        fin_cases i
        · exact hea0
        · exact heb0)
  rw [standardLubinTateEndomorphismEvalAt,
    SameUniformizer.standardLubinTateEndomorphism_add]
  simp only [standardLubinTateFormalAdd,
    standardLubinTateLevelPowerSeriesEval,
    PowerSeries.coe_eval₂Hom]
  have hcoeff :
      algebraMap F.valuationSubring
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring =
        standardLubinTateLevelCoefficientHom hπ n := by
    rfl
  have hsubst :=
    MvPowerSeries.eval₂_subst
      (R := F.valuationSubring) (S := F.valuationSubring)
      (T :=
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
      (a := (![ea, eb] :
        Fin 2 → PowerSeries F.valuationSubring))
      hab (b := fun _ : Unit => x) (PowerSeries.hasEval hx)
      (SameUniformizer.standardFormalGroupPowerSeries hπ)
  rw [hcoeff] at hsubst
  have hvalues :
      (fun s : Fin 2 =>
        MvPowerSeries.eval₂
          (standardLubinTateLevelCoefficientHom hπ n)
          (fun _ : Unit => x) (![ea, eb] s)) =
        ![
          MvPowerSeries.eval₂
            (standardLubinTateLevelCoefficientHom hπ n)
            (fun _ : Unit => x) ea,
          MvPowerSeries.eval₂
            (standardLubinTateLevelCoefficientHom hπ n)
            (fun _ : Unit => x) eb] := by
    funext s
    fin_cases s <;> rfl
  rw [hvalues] at hsubst
  simpa only [ea, eb, standardLubinTateEndomorphismEvalAt,
    standardLubinTateLevelPowerSeriesEval,
    PowerSeries.coe_eval₂Hom, PowerSeries.eval₂,
    Function.const_apply] using hsubst

/-- At the primitive point, addition of scalars is analytic formal-group
addition of their values. -/
theorem standardLubinTateEndomorphismValue_add
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (a b : F.valuationSubring) :
    standardLubinTateEndomorphismValue hπ n (a + b) =
      standardLubinTateFormalAdd hπ n
        (standardLubinTateEndomorphismValue hπ n a)
        (standardLubinTateEndomorphismValue hπ n b) :=
  standardLubinTateEndomorphismEvalAt_add hπ n
    (standardLubinTatePrimitivePointInteger hπ n)
    (standardLubinTatePrimitivePointInteger_hasEval hπ n) a b

private theorem standardLubinTateEndomorphismEvalAt_eq_of_point_eq
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (x y : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
    (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
    (hxy : x = y) (a : F.valuationSubring) :
    standardLubinTateEndomorphismEvalAt hπ n x hx a =
      standardLubinTateEndomorphismEvalAt hπ n y hy a := by
  subst y
  rfl

/-- Every standard scalar endomorphism fixes the zero point. -/
theorem standardLubinTateEndomorphismEvalAt_zero_point
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (a : F.valuationSubring) :
    standardLubinTateEndomorphismEvalAt hπ n 0
        PowerSeries.HasEval.zero a = 0 := by
  have h :=
    standardLubinTateEndomorphismEvalAt_mul hπ n 0
      PowerSeries.HasEval.zero a 0
  simpa using h.symm

/-- A unit scalar acts injectively on the topologically nilpotent elements
of a finite-level integer ring. -/
theorem standardLubinTateEndomorphismEvalAt_unit_injective
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (u : F.valuationSubringˣ)
    {x y : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring}
    (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
    (hxy :
      standardLubinTateEndomorphismEvalAt hπ n x hx
          (u : F.valuationSubring) =
        standardLubinTateEndomorphismEvalAt hπ n y hy
          (u : F.valuationSubring)) :
    x = y := by
  let ux :=
    standardLubinTateEndomorphismEvalAt hπ n x hx
      (u : F.valuationSubring)
  let uy :=
    standardLubinTateEndomorphismEvalAt hπ n y hy
      (u : F.valuationSubring)
  let hux : PowerSeries.HasEval ux :=
    standardLubinTateEndomorphismEvalAt_hasEval hπ n x hx
      (u : F.valuationSubring)
  let huy : PowerSeries.HasEval uy :=
    standardLubinTateEndomorphismEvalAt_hasEval hπ n y hy
      (u : F.valuationSubring)
  calc
    x =
        standardLubinTateEndomorphismEvalAt hπ n x hx
          (((u⁻¹ : F.valuationSubringˣ) : F.valuationSubring) *
            (u : F.valuationSubring)) := by simp
    _ =
        standardLubinTateEndomorphismEvalAt hπ n ux hux
          ((u⁻¹ : F.valuationSubringˣ) : F.valuationSubring) :=
      standardLubinTateEndomorphismEvalAt_mul hπ n x hx
        ((u⁻¹ : F.valuationSubringˣ) : F.valuationSubring)
        (u : F.valuationSubring)
    _ =
        standardLubinTateEndomorphismEvalAt hπ n uy huy
          ((u⁻¹ : F.valuationSubringˣ) : F.valuationSubring) := by
      apply
        standardLubinTateEndomorphismEvalAt_eq_of_point_eq
          hπ n ux uy hux huy
      exact hxy
    _ =
        standardLubinTateEndomorphismEvalAt hπ n y hy
          (((u⁻¹ : F.valuationSubringˣ) : F.valuationSubring) *
            (u : F.valuationSubring)) :=
      (standardLubinTateEndomorphismEvalAt_mul hπ n y hy
        ((u⁻¹ : F.valuationSubringˣ) : F.valuationSubring)
        (u : F.valuationSubring)).symm
    _ = y := by simp

/-- Evaluating `[π ^ r]` is the same as evaluating the `r`-fold standard
division-polynomial iterate. -/
theorem standardLubinTateEndomorphismEvalAt_uniformizer_pow
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (x : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
    (hx : PowerSeries.HasEval x) (r : ℕ) :
    standardLubinTateEndomorphismEvalAt hπ n x hx (π ^ r) =
      Polynomial.eval₂
        (standardLubinTateLevelCoefficientHom hπ n) x
        (standardLubinTatePolynomialIterate F π r) := by
  induction r with
  | zero =>
      simp [standardLubinTatePolynomialIterate_zero]
  | succ r ih =>
      rw [pow_succ',
        standardLubinTateEndomorphismEvalAt_mul]
      rw [standardLubinTateEndomorphismEvalAt,
        SameUniformizer.standardLubinTateEndomorphism_uniformizer,
        ← standardLubinTatePolynomial_toPowerSeries_eq_series hπ,
        standardLubinTateLevelPowerSeriesEval_coe, ih,
        standardLubinTatePolynomialIterate_succ,
        Polynomial.eval₂_comp]

/-- A valuation-ring unit acts on the chosen primitive point by analytic
evaluation of its standard scalar endomorphism. -/
noncomputable def standardLubinTatePrimitivePointIntegerAction
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (u : F.valuationSubringˣ) :
    (standardLubinTateLevelCompleteDVF hπ n).valuationSubring :=
  standardLubinTateEndomorphismValue hπ n
    (u : F.valuationSubring)

/-- A unit translate of the primitive point is still topologically
nilpotent. -/
theorem standardLubinTatePrimitivePointIntegerAction_hasEval
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (u : F.valuationSubringˣ) :
    PowerSeries.HasEval
      (standardLubinTatePrimitivePointIntegerAction hπ n u) :=
  standardLubinTateEndomorphismValue_hasEval hπ n
    (u : F.valuationSubring)

/-- The unit `1` fixes the chosen primitive point. -/
@[simp]
theorem standardLubinTatePrimitivePointIntegerAction_one
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    standardLubinTatePrimitivePointIntegerAction hπ n 1 =
      standardLubinTatePrimitivePointInteger hπ n := by
  simp [standardLubinTatePrimitivePointIntegerAction]

/-- Multiplication of unit parameters is composition of their analytic
actions. -/
theorem standardLubinTatePrimitivePointIntegerAction_mul
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (u w : F.valuationSubringˣ) :
    standardLubinTatePrimitivePointIntegerAction hπ n (u * w) =
      standardLubinTateEndomorphismEvalAt hπ n
        (standardLubinTatePrimitivePointIntegerAction hπ n w)
        (standardLubinTatePrimitivePointIntegerAction_hasEval hπ n w)
        (u : F.valuationSubring) := by
  simpa [standardLubinTatePrimitivePointIntegerAction] using
    standardLubinTateEndomorphismValue_mul hπ n
      (u : F.valuationSubring) (w : F.valuationSubring)

/-- The primitive level-`n + 1` point has exact scalar annihilator
`m^(n + 1)`. -/
theorem standardLubinTateEndomorphismValue_eq_zero_iff_mem_maximalIdeal_pow
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (a : F.valuationSubring) :
    standardLubinTateEndomorphismValue hπ n a = 0 ↔
      a ∈ F.toCompleteDVF.maximalIdeal ^ (n + 1) := by
  let lambda := standardLubinTatePrimitivePointInteger hπ n
  let hlambda := standardLubinTatePrimitivePointInteger_hasEval hπ n
  constructor
  · intro haZero
    by_cases ha : a = 0
    · subst a
      exact (F.toCompleteDVF.maximalIdeal ^ (n + 1)).zero_mem
    have hπirr : Irreducible π :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2
        (F.toCompleteDVF.maximalIdeal_eq_span_uniformizer hπ)
    obtain ⟨r, u, hu⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπirr
    let z :=
      standardLubinTateEndomorphismEvalAt hπ n lambda hlambda
        (π ^ r)
    let hz : PowerSeries.HasEval z :=
      standardLubinTateEndomorphismEvalAt_hasEval hπ n
        lambda hlambda (π ^ r)
    have huzero :
        standardLubinTateEndomorphismEvalAt hπ n z hz
            (u : F.valuationSubring) = 0 := by
      calc
        standardLubinTateEndomorphismEvalAt hπ n z hz
            (u : F.valuationSubring) =
            standardLubinTateEndomorphismValue hπ n
              ((u : F.valuationSubring) * π ^ r) := by
          exact
            (standardLubinTateEndomorphismEvalAt_mul hπ n
              lambda hlambda (u : F.valuationSubring) (π ^ r)).symm
        _ = standardLubinTateEndomorphismValue hπ n a := by
          rw [hu]
        _ = 0 := haZero
    have hzZero : z = 0 := by
      apply
        standardLubinTateEndomorphismEvalAt_unit_injective
          hπ n u hz PowerSeries.HasEval.zero
      rw [huzero,
        standardLubinTateEndomorphismEvalAt_zero_point]
    have hnr : n + 1 ≤ r := by
      by_contra hnot
      have hrn : r ≤ n := by omega
      have hne :=
        standardLubinTatePrimitivePointInteger_iterate_ne_zero_of_le
          hπ n hrn
      apply hne
      change
        Polynomial.eval₂
            (standardLubinTateLevelCoefficientHom hπ n) lambda
            (standardLubinTatePolynomialIterate F π r) = 0
      calc
        _ =
            standardLubinTateEndomorphismEvalAt hπ n lambda hlambda
              (π ^ r) :=
          (standardLubinTateEndomorphismEvalAt_uniformizer_pow
            hπ n lambda hlambda r).symm
        _ = 0 := by simpa [z] using hzZero
    rw [F.toCompleteDVF.maximalIdeal_eq_span_uniformizer hπ,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rw [hu]
    rcases pow_dvd_pow π hnr with ⟨c, hc⟩
    refine ⟨(u : F.valuationSubring) * c, ?_⟩
    rw [hc]
    ring
  · intro ha
    rw [F.toCompleteDVF.maximalIdeal_eq_span_uniformizer hπ,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
    rcases ha with ⟨d, hd⟩
    have ha' : a = d * π ^ (n + 1) := by
      rw [hd, mul_comm]
    have hkill :
        standardLubinTateEndomorphismValue hπ n (π ^ (n + 1)) =
          0 := by
      rw [standardLubinTateEndomorphismValue,
        standardLubinTateEndomorphismEvalAt_uniformizer_pow]
      simpa [standardLubinTateLevelCoefficientHom] using
        standardLubinTatePrimitivePointInteger_iterate_succ_eq_zero
          hπ n
    calc
      standardLubinTateEndomorphismValue hπ n a =
          standardLubinTateEndomorphismValue hπ n
            (d * π ^ (n + 1)) := by rw [ha']
      _ =
          standardLubinTateEndomorphismEvalAt hπ n
            (standardLubinTateEndomorphismValue hπ n
              (π ^ (n + 1)))
            (standardLubinTateEndomorphismValue_hasEval hπ n
              (π ^ (n + 1))) d :=
        standardLubinTateEndomorphismValue_mul hπ n d
          (π ^ (n + 1))
      _ =
          standardLubinTateEndomorphismEvalAt hπ n 0
            PowerSeries.HasEval.zero d := by
        apply
          standardLubinTateEndomorphismEvalAt_eq_of_point_eq
            hπ n
        exact hkill
      _ = 0 :=
        standardLubinTateEndomorphismEvalAt_zero_point hπ n d

/-- A unit fixes the primitive level-`n + 1` point exactly when it belongs
to `U^(n + 1)`. -/
theorem
    standardLubinTatePrimitivePointIntegerAction_eq_self_iff_mem_higherPrincipalUnitGroup
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (u : F.valuationSubringˣ) :
    standardLubinTatePrimitivePointIntegerAction hπ n u =
        standardLubinTatePrimitivePointInteger hπ n ↔
      u ∈ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF
        (n + 1) := by
  rw [CompleteDVF.higherPrincipalUnitGroup.mem_iff]
  constructor
  · intro hu
    apply
      (standardLubinTateEndomorphismValue_eq_zero_iff_mem_maximalIdeal_pow
        hπ n ((u : F.valuationSubring) - 1)).mp
    have huone :
        standardLubinTateEndomorphismValue hπ n
            (u : F.valuationSubring) =
          standardLubinTateEndomorphismValue hπ n 1 := by
      calc
        standardLubinTateEndomorphismValue hπ n
            (u : F.valuationSubring) =
            standardLubinTatePrimitivePointIntegerAction hπ n u :=
          rfl
        _ = standardLubinTatePrimitivePointInteger hπ n := hu
        _ = standardLubinTateEndomorphismValue hπ n 1 :=
          (standardLubinTateEndomorphismValue_one hπ n).symm
    calc
      standardLubinTateEndomorphismValue hπ n
          ((u : F.valuationSubring) - 1) =
          standardLubinTateFormalAdd hπ n
            (standardLubinTateEndomorphismValue hπ n
              (u : F.valuationSubring))
            (standardLubinTateEndomorphismValue hπ n (-1)) := by
              simpa [sub_eq_add_neg] using
                standardLubinTateEndomorphismValue_add hπ n
                  (u : F.valuationSubring) (-1)
      _ =
          standardLubinTateFormalAdd hπ n
            (standardLubinTateEndomorphismValue hπ n 1)
            (standardLubinTateEndomorphismValue hπ n (-1)) := by
              rw [huone]
      _ = standardLubinTateEndomorphismValue hπ n (1 + (-1)) :=
        (standardLubinTateEndomorphismValue_add hπ n 1 (-1)).symm
      _ = 0 := by simp
  · intro hu
    have hzero :
        standardLubinTateEndomorphismValue hπ n
            ((u : F.valuationSubring) - 1) = 0 :=
      (standardLubinTateEndomorphismValue_eq_zero_iff_mem_maximalIdeal_pow
        hπ n ((u : F.valuationSubring) - 1)).2 hu
    change
      standardLubinTateEndomorphismValue hπ n
          (u : F.valuationSubring) =
        standardLubinTatePrimitivePointInteger hπ n
    calc
      standardLubinTateEndomorphismValue hπ n
          (u : F.valuationSubring) =
          standardLubinTateEndomorphismValue hπ n
            (1 + ((u : F.valuationSubring) - 1)) := by
              congr 1
              ring
      _ =
          standardLubinTateFormalAdd hπ n
            (standardLubinTateEndomorphismValue hπ n 1)
            (standardLubinTateEndomorphismValue hπ n
              ((u : F.valuationSubring) - 1)) :=
        standardLubinTateEndomorphismValue_add hπ n 1
          ((u : F.valuationSubring) - 1)
      _ =
          standardLubinTateFormalAdd hπ n
            (standardLubinTateEndomorphismValue hπ n 1)
            (standardLubinTateEndomorphismValue hπ n 0) := by
              rw [hzero, standardLubinTateEndomorphismValue_zero]
      _ = standardLubinTateEndomorphismValue hπ n (1 + 0) :=
        (standardLubinTateEndomorphismValue_add hπ n 1 0).symm
      _ = standardLubinTatePrimitivePointInteger hπ n := by simp

/-- Two unit actions give the same primitive integer point exactly when
their quotient lies in `U^(n + 1)`. -/
theorem
    standardLubinTatePrimitivePointIntegerAction_eq_iff_div_mem_higherPrincipalUnitGroup
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (u w : F.valuationSubringˣ) :
    standardLubinTatePrimitivePointIntegerAction hπ n u =
        standardLubinTatePrimitivePointIntegerAction hπ n w ↔
      u / w ∈ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF
        (n + 1) := by
  constructor
  · intro huw
    apply
      (standardLubinTatePrimitivePointIntegerAction_eq_self_iff_mem_higherPrincipalUnitGroup
        hπ n (u / w)).mp
    calc
      standardLubinTatePrimitivePointIntegerAction hπ n (u / w) =
          standardLubinTatePrimitivePointIntegerAction hπ n
            (w⁻¹ * u) := by
              congr 1
              simp [div_eq_mul_inv, mul_comm]
      _ =
          standardLubinTateEndomorphismEvalAt hπ n
            (standardLubinTatePrimitivePointIntegerAction hπ n u)
            (standardLubinTatePrimitivePointIntegerAction_hasEval hπ n u)
            ((w⁻¹ : F.valuationSubringˣ) : F.valuationSubring) :=
        standardLubinTatePrimitivePointIntegerAction_mul hπ n w⁻¹ u
      _ =
          standardLubinTateEndomorphismEvalAt hπ n
            (standardLubinTatePrimitivePointIntegerAction hπ n w)
            (standardLubinTatePrimitivePointIntegerAction_hasEval hπ n w)
            ((w⁻¹ : F.valuationSubringˣ) : F.valuationSubring) := by
              apply
                standardLubinTateEndomorphismEvalAt_eq_of_point_eq
                  hπ n
              exact huw
      _ =
          standardLubinTatePrimitivePointIntegerAction hπ n (w⁻¹ * w) :=
        (standardLubinTatePrimitivePointIntegerAction_mul
          hπ n w⁻¹ w).symm
      _ = standardLubinTatePrimitivePointInteger hπ n := by simp
  · intro huw
    have hfixed :=
      (standardLubinTatePrimitivePointIntegerAction_eq_self_iff_mem_higherPrincipalUnitGroup
        hπ n (u / w)).2 huw
    calc
      standardLubinTatePrimitivePointIntegerAction hπ n u =
          standardLubinTatePrimitivePointIntegerAction hπ n
            (w * (u / w)) := by
              congr 1
              simp [div_eq_mul_inv, mul_left_comm]
      _ =
          standardLubinTateEndomorphismEvalAt hπ n
            (standardLubinTatePrimitivePointIntegerAction hπ n (u / w))
            (standardLubinTatePrimitivePointIntegerAction_hasEval
              hπ n (u / w))
            (w : F.valuationSubring) :=
        standardLubinTatePrimitivePointIntegerAction_mul hπ n w (u / w)
      _ =
          standardLubinTateEndomorphismEvalAt hπ n
            (standardLubinTatePrimitivePointInteger hπ n)
            (standardLubinTatePrimitivePointInteger_hasEval hπ n)
            (w : F.valuationSubring) := by
              apply
                standardLubinTateEndomorphismEvalAt_eq_of_point_eq
                  hπ n
              exact hfixed
      _ = standardLubinTatePrimitivePointIntegerAction hπ n w := rfl

/-- The analytic unit action, viewed in the finite-level field. -/
noncomputable def standardLubinTatePrimitiveLevelAction
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (u : F.valuationSubringˣ) :
    standardLubinTateLevelField hπ n :=
  (standardLubinTatePrimitivePointIntegerAction hπ n u :
    standardLubinTateLevelField hπ n)

/-- The natural embedding of the finite-level integer ring into the fixed
separable closure. -/
noncomputable def standardLubinTateLevelIntegerToSeparableClosure
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    (standardLubinTateLevelCompleteDVF hπ n).valuationSubring →+*
      SeparableClosure K :=
  (standardLubinTateLevelField hπ n).val.toRingHom.comp
    (standardLubinTateLevelCompleteDVF hπ n).valuation.valuationSubring.subtype

/-- The natural embedding of the finite-level integer ring into the fixed
separable closure is injective. -/
theorem standardLubinTateLevelIntegerToSeparableClosure_injective
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    Function.Injective
      (standardLubinTateLevelIntegerToSeparableClosure hπ n) := by
  intro x y hxy
  change
    (standardLubinTateLevelField hπ n).val
        (x : standardLubinTateLevelField hπ n) =
      (standardLubinTateLevelField hπ n).val
        (y : standardLubinTateLevelField hπ n) at hxy
  apply Subtype.ext
  exact (standardLubinTateLevelField hπ n).val.injective hxy

/-- On base coefficients, the level-integer embedding is the fixed
embedding of the base field into its separable closure. -/
theorem standardLubinTateLevelIntegerToSeparableClosure_comp_coefficientHom
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    (standardLubinTateLevelIntegerToSeparableClosure hπ n).comp
        (standardLubinTateLevelCoefficientHom hπ n) =
      (algebraMap K (SeparableClosure K)).comp
        (algebraMap F.valuationSubring K) := by
  apply RingHom.ext
  intro a
  simp only [RingHom.comp_apply]
  change
    ((standardLubinTateLevelField hπ n).val
      (((standardLubinTateLevelCoefficientHom hπ n) a :
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring) :
        standardLubinTateLevelField hπ n)) =
      algebraMap K (SeparableClosure K)
        (algebraMap F.valuationSubring K a)
  rw [standardLubinTateLevelCoefficientHom_apply]
  exact (standardLubinTateLevelField hπ n).val.commutes
    (algebraMap F.valuationSubring K a)

/-- The analytic unit action, transported from the level integer ring to
the chosen finite-level field. -/
noncomputable def standardLubinTatePrimitiveRootAction
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (u : F.valuationSubringˣ) :
    SeparableClosure K :=
  standardLubinTateLevelIntegerToSeparableClosure hπ n
    (standardLubinTatePrimitivePointIntegerAction hπ n u)

/-- Coercing the finite-level action to the fixed separable closure gives
the primitive-root action. -/
@[simp]
theorem standardLubinTatePrimitiveLevelAction_coe
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (u : F.valuationSubringˣ) :
    ((standardLubinTatePrimitiveLevelAction hπ n u :
        standardLubinTateLevelField hπ n) : SeparableClosure K) =
      standardLubinTatePrimitiveRootAction hπ n u :=
  rfl

/-- The identity unit fixes the chosen primitive root. -/
@[simp]
theorem standardLubinTatePrimitiveRootAction_one
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    standardLubinTatePrimitiveRootAction hπ n 1 =
      chosenStandardLubinTatePrimitiveRoot hπ n := by
  change
    standardLubinTateLevelIntegerToSeparableClosure hπ n
        (standardLubinTatePrimitivePointIntegerAction hπ n 1) =
      chosenStandardLubinTatePrimitiveRoot hπ n
  rw [standardLubinTatePrimitivePointIntegerAction_one]
  change
    ((standardLubinTatePrimitivePointInteger hπ n :
        standardLubinTateLevelField hπ n) : SeparableClosure K) =
      chosenStandardLubinTatePrimitiveRoot hπ n
  rw [standardLubinTatePrimitivePointInteger_coe]
  exact standardLubinTateLevelGenerator_coe hπ n

/-- Equality of primitive-root actions can be checked already in the
finite-level integer ring. -/
theorem standardLubinTatePrimitiveRootAction_eq_iff_integerAction_eq
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (u w : F.valuationSubringˣ) :
    standardLubinTatePrimitiveRootAction hπ n u =
        standardLubinTatePrimitiveRootAction hπ n w ↔
      standardLubinTatePrimitivePointIntegerAction hπ n u =
        standardLubinTatePrimitivePointIntegerAction hπ n w := by
  change
    standardLubinTateLevelIntegerToSeparableClosure hπ n
        (standardLubinTatePrimitivePointIntegerAction hπ n u) =
      standardLubinTateLevelIntegerToSeparableClosure hπ n
        (standardLubinTatePrimitivePointIntegerAction hπ n w) ↔
      standardLubinTatePrimitivePointIntegerAction hπ n u =
        standardLubinTatePrimitivePointIntegerAction hπ n w
  constructor
  · intro h
    exact
      (standardLubinTateLevelIntegerToSeparableClosure_injective hπ n) h
  · exact congrArg (standardLubinTateLevelIntegerToSeparableClosure hπ n)

/-- Two unit actions give the same primitive root exactly when their
quotient lies in `U^(n + 1)`. -/
theorem
    standardLubinTatePrimitiveRootAction_eq_iff_div_mem_higherPrincipalUnitGroup
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (u w : F.valuationSubringˣ) :
    standardLubinTatePrimitiveRootAction hπ n u =
        standardLubinTatePrimitiveRootAction hπ n w ↔
      u / w ∈ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF
        (n + 1) := by
  rw [standardLubinTatePrimitiveRootAction_eq_iff_integerAction_eq,
    standardLubinTatePrimitivePointIntegerAction_eq_iff_div_mem_higherPrincipalUnitGroup]

/-- Unit parameters in the same higher-principal-unit coset give the same
primitive root. -/
theorem
    standardLubinTatePrimitiveRootAction_eq_of_div_mem_higherPrincipalUnitGroup
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    {u w : F.valuationSubringˣ}
    (huw :
      u / w ∈ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF
        (n + 1)) :
    standardLubinTatePrimitiveRootAction hπ n u =
      standardLubinTatePrimitiveRootAction hπ n w :=
  (standardLubinTatePrimitiveRootAction_eq_iff_div_mem_higherPrincipalUnitGroup
    hπ n u w).2 huw

/-- A unit translate of the chosen primitive point is again a root of the
level-`n + 1` primitive division polynomial. -/
theorem standardLubinTatePrimitiveRootAction_isRoot
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (u : F.valuationSubringˣ) :
    ((standardLubinTatePrimitivePolynomialOverField F π n).map
      (algebraMap K (SeparableClosure K))).IsRoot
        (standardLubinTatePrimitiveRootAction hπ n u) := by
  let lambda := standardLubinTatePrimitivePointInteger hπ n
  let hlambda : PowerSeries.HasEval lambda :=
    standardLubinTatePrimitivePointInteger_hasEval hπ n
  let y := standardLubinTatePrimitivePointIntegerAction hπ n u
  let hy : PowerSeries.HasEval y :=
    standardLubinTatePrimitivePointIntegerAction_hasEval hπ n u
  have hkillLambda :
      standardLubinTateEndomorphismValue hπ n (π ^ (n + 1)) = 0 := by
    rw [standardLubinTateEndomorphismValue,
      standardLubinTateEndomorphismEvalAt_uniformizer_pow]
    simpa [standardLubinTateLevelCoefficientHom] using
      standardLubinTatePrimitivePointInteger_iterate_succ_eq_zero hπ n
  have hySucc :
      Polynomial.eval₂
          (standardLubinTateLevelCoefficientHom hπ n) y
          (standardLubinTatePolynomialIterate F π (n + 1)) = 0 := by
    rw [← standardLubinTateEndomorphismEvalAt_uniformizer_pow
      hπ n y hy (n + 1)]
    calc
      standardLubinTateEndomorphismEvalAt hπ n y hy
          (π ^ (n + 1)) =
          standardLubinTateEndomorphismValue hπ n
            (π ^ (n + 1) * (u : F.valuationSubring)) := by
        simpa [y, standardLubinTatePrimitivePointIntegerAction] using
          (standardLubinTateEndomorphismValue_mul hπ n
            (π ^ (n + 1)) (u : F.valuationSubring)).symm
      _ =
          standardLubinTateEndomorphismValue hπ n
            ((u : F.valuationSubring) * π ^ (n + 1)) := by
        rw [mul_comm]
      _ =
          standardLubinTateEndomorphismEvalAt hπ n
            (standardLubinTateEndomorphismValue hπ n (π ^ (n + 1)))
            (standardLubinTateEndomorphismValue_hasEval hπ n
              (π ^ (n + 1)))
            (u : F.valuationSubring) :=
        standardLubinTateEndomorphismValue_mul hπ n
          (u : F.valuationSubring) (π ^ (n + 1))
      _ =
          standardLubinTateEndomorphismEvalAt hπ n 0
            PowerSeries.HasEval.zero (u : F.valuationSubring) := by
        apply
          standardLubinTateEndomorphismEvalAt_eq_of_point_eq
            hπ n
        exact hkillLambda
      _ = 0 :=
        standardLubinTateEndomorphismEvalAt_zero_point hπ n
          (u : F.valuationSubring)
  have hyN :
      Polynomial.eval₂
          (standardLubinTateLevelCoefficientHom hπ n) y
          (standardLubinTatePolynomialIterate F π n) ≠ 0 := by
    intro hyNZero
    have hyEvalZero :
        standardLubinTateEndomorphismEvalAt hπ n y hy (π ^ n) = 0 := by
      rw [standardLubinTateEndomorphismEvalAt_uniformizer_pow]
      exact hyNZero
    let z := standardLubinTateEndomorphismValue hπ n (π ^ n)
    let hz : PowerSeries.HasEval z :=
      standardLubinTateEndomorphismValue_hasEval hπ n (π ^ n)
    have huzero :
        standardLubinTateEndomorphismEvalAt hπ n z hz
            (u : F.valuationSubring) = 0 := by
      calc
        standardLubinTateEndomorphismEvalAt hπ n z hz
            (u : F.valuationSubring) =
            standardLubinTateEndomorphismValue hπ n
              ((u : F.valuationSubring) * π ^ n) := by
          simpa [z] using
            (standardLubinTateEndomorphismValue_mul hπ n
              (u : F.valuationSubring) (π ^ n)).symm
        _ =
            standardLubinTateEndomorphismValue hπ n
              (π ^ n * (u : F.valuationSubring)) := by
          rw [mul_comm]
        _ =
            standardLubinTateEndomorphismEvalAt hπ n y hy (π ^ n) := by
          simpa [y, standardLubinTatePrimitivePointIntegerAction] using
            standardLubinTateEndomorphismValue_mul hπ n
              (π ^ n) (u : F.valuationSubring)
        _ = 0 := hyEvalZero
    have hzZero : z = 0 := by
      apply
        standardLubinTateEndomorphismEvalAt_unit_injective
          hπ n u hz PowerSeries.HasEval.zero
      rw [huzero,
        standardLubinTateEndomorphismEvalAt_zero_point]
    have hne :=
      standardLubinTatePrimitivePointInteger_iterate_ne_zero_of_le
        hπ n (show n ≤ n from le_rfl)
    apply hne
    change
      Polynomial.eval₂
          (standardLubinTateLevelCoefficientHom hπ n) lambda
          (standardLubinTatePolynomialIterate F π n) = 0
    calc
      _ =
          standardLubinTateEndomorphismEvalAt hπ n lambda hlambda
            (π ^ n) :=
        (standardLubinTateEndomorphismEvalAt_uniformizer_pow
          hπ n lambda hlambda n).symm
      _ = standardLubinTateEndomorphismValue hπ n (π ^ n) := rfl
      _ = 0 := by simpa [z] using hzZero
  have hfactor :=
    congrArg
      (Polynomial.eval₂
        (standardLubinTateLevelCoefficientHom hπ n) y)
      (standardLubinTatePolynomialIterate_succ_factor F π n)
  rw [hySucc, Polynomial.eval₂_mul] at hfactor
  have hprimitive :
      Polynomial.eval₂
          (standardLubinTateLevelCoefficientHom hπ n) y
          (standardLubinTatePrimitivePolynomial F π n) = 0 :=
    (mul_eq_zero.mp hfactor.symm).resolve_left hyN
  have hprimitiveMap :=
    congrArg (standardLubinTateLevelIntegerToSeparableClosure hπ n)
      hprimitive
  rw [map_zero, Polynomial.hom_eval₂,
    standardLubinTateLevelIntegerToSeparableClosure_comp_coefficientHom]
      at hprimitiveMap
  simpa [Polynomial.IsRoot,
    standardLubinTatePrimitivePolynomialOverField,
    standardLubinTatePrimitiveRootAction,
    Polynomial.eval_map, Polynomial.eval₂_map, y] using hprimitiveMap

end AnalyticAction

end LubinTate

end
