/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestriction
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CyclicValueGroup
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuation
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.SeriesValuationEstimates
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuationUniformizer
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CompleteRangeRestriction
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.UniformizerIntegerValuation
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestrictedTopology
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuationSubringUnitMap
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.LocalFieldRangeRestriction
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuedExtensionUnitMap
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.CompleteDVRExpansion
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.LinearAlgebra.Dimension.Basic
/-!
# Equal-characteristic Laurent-series input for the local-field structure classification

This file starts the equal-characteristic branch of the local-field structure classification, the local-field structure classification.  Given the Teichmuller coefficient-field section
`κ -> O_K -> K` and a uniformizer `π`, it constructs the induced evaluation
map `κ((X)) -> K` by first evaluating `κ⟦X⟧` at `X = π`, then using the
localization description `κ((X)) = κ⟦X⟧[X⁻¹]`.
-/

noncomputable section

universe u v

open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace CompleteDVF

open scoped PowerSeries LaurentSeries Filter Topology BigOperators
open Filter

variable {K : Type u} [Field K]
variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

namespace EqualCharacteristicLaurent

/-- The Teichmuller coefficient-field section `κ -> O_K` used before passing
to the fraction field. -/
abbrev coeffSubringHom [Finite F.residueField] (p : ℕ) [Fact p.Prime]
    [CharP F.valuationSubring p] {n : ℕ+}
    (hcard : Nat.card F.residueField = p ^ (n : ℕ)) :
    F.residueField →+* F.valuationSubring :=
  LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP
    (F := F) p hcard

/-- The Teichmuller coefficient-field embedding `κ -> K` used in the
equal-characteristic Laurent-series branch. -/
abbrev coeffHom [Finite F.residueField] (p : ℕ) [Fact p.Prime]
    [CharP F.valuationSubring p] {n : ℕ+}
    (hcard : Nat.card F.residueField = p ^ (n : ℕ)) :
    F.residueField →+* K :=
  LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP
    (F := F) p hcard

/-- The Teichmuller section is a representative system for the residue field. -/
noncomputable def teichmullerRepresentativeSystem [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ)) :
    LubinTate.Valuations.residueRepresentativeSystem F where
  repr := coeffSubringHom (F := F) p hcard
  residue_repr := by
    intro a
    have hcomp :=
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueMap_comp_residueTeichmullerRingHomOfCharP
        (F := F) p hcard
    simpa [coeffSubringHom, RingHom.comp_apply] using
      congrFun (congrArg DFunLike.coe hcomp) a
  repr_zero := by
    simp [coeffSubringHom]

/-- The field-valued coefficient embedding is the valuation-ring coefficient
section followed by the valuation-subring inclusion. -/
@[simp] theorem coeffHom_apply [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (a : F.residueField) :
    coeffHom (F := F) p hcard a =
      (coeffSubringHom (F := F) p hcard a : K) := by
  rfl

/-- The Teichmuller coefficient-field embedding is continuous when the finite
residue field is given the discrete uniformity. -/
theorem continuous_coeffHom_of_discrete [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    [UniformSpace F.residueField] [DiscreteUniformity F.residueField]
    [TopologicalSpace K] :
    Continuous (coeffHom (F := F) p hcard) :=
  continuous_of_discreteTopology

/-- The valuation-ring Teichmuller coefficient section is continuous from the
discrete residue-field topology to any topology on the valuation ring. -/
theorem continuous_coeffSubringHom_of_discrete [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    [UniformSpace F.residueField] [DiscreteUniformity F.residueField]
    [TopologicalSpace F.valuationSubring] :
    Continuous (coeffSubringHom (F := F) p hcard) :=
  continuous_of_discreteTopology

/-- A complete-DVF uniformizer is topologically nilpotent for the
range-restricted valued topology. -/
theorem uniformizer_hasEval_mrangeRestrict
    {π : F.valuationSubring}
    (hπ : F.valuation.IsUniformizer (π : K)) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    PowerSeries.HasEval (π : K) := by
  let Γ : Type v :=
    MonoidHom.mrange F.valuation.toMonoidWithZeroHom
  let : Valued K Γ := (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  have : IsCyclic Γˣ := by
    simpa [Γ] using
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_units_isCyclic F
  have : MulArchimedean Γ :=
    _root_.LocalFieldTheory.DiscreteValuationField.WithZeroValuation.units_isCyclic_mulArchimedean Γ
  have hπ_lt :
      (Valued.v : _root_.Valuation K Γ) (π : K) < 1 := by
    change _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F (π : K) < (1 : Γ)
    rw [← Subtype.coe_lt_coe]
    simpa [Γ, _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict] using hπ.val_lt_one
  exact Valued.tendsto_zero_pow_of_v_lt_one hπ_lt

/-- The maximal-ideal adic topology on the valuation ring is linear. -/
private theorem valuationSubring_isLinearTopology_adic :
    letI : TopologicalSpace F.valuationSubring := F.maximalIdeal.adicTopology
    IsLinearTopology F.valuationSubring F.valuationSubring := by
  let : TopologicalSpace F.valuationSubring := F.maximalIdeal.adicTopology
  exact
    IsLinearTopology.mk_of_hasBasis F.valuationSubring
      (Ideal.hasBasis_nhds_zero_adic F.maximalIdeal)

/-- The `WithIdeal` adic topology on the valuation ring is linear. -/
private theorem valuationSubring_isLinearTopology_withIdeal :
    letI : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
    IsLinearTopology F.valuationSubring F.valuationSubring := by
  let : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
  exact valuationSubring_isLinearTopology_adic (F := F)

/-- The valuation ring is complete for its maximal-ideal adic topology. -/
private theorem valuationSubring_completeSpace_withIdeal :
    letI : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
    CompleteSpace F.valuationSubring := by
  let : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
  have hadic : IsAdic F.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp F.isAdicComplete).1

/-- The valuation ring is Hausdorff for its maximal-ideal adic topology. -/
private theorem valuationSubring_t2Space_withIdeal :
    letI : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
    T2Space F.valuationSubring := by
  let : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
  have hadic : IsAdic F.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp F.isAdicComplete).2

/-- A complete-DVF uniformizer is topologically nilpotent in the valuation
ring for the maximal-ideal adic topology. -/
theorem uniformizer_hasEval_valuationSubring_withIdeal
    {π : F.valuationSubring}
    (hπ : F.valuation.IsUniformizer (π : K)) :
    letI : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
    PowerSeries.HasEval π := by
  let : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
  change Filter.Tendsto (fun m : ℕ => π ^ m) Filter.atTop
    (nhds (0 : F.valuationSubring))
  refine (F.maximalIdeal.hasBasis_nhds_zero_adic).tendsto_right_iff.2 ?_
  intro n _
  refine Filter.eventually_atTop.2 ⟨n, fun m hm => ?_⟩
  have hπmem : π ∈ F.maximalIdeal :=
    F.uniformizer_mem_maximalIdeal hπ
  have hpow : π ^ m ∈ F.maximalIdeal ^ m :=
    Ideal.pow_mem_pow hπmem m
  exact Ideal.pow_le_pow_right hm hpow

/-- Evaluation of power series into the valuation ring through the
Teichmuller coefficient section, sending `X` to a chosen uniformizer. -/
noncomputable def powerSeriesEvalSubringHom [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    [UniformSpace F.residueField] [IsUniformAddGroup F.residueField]
    [IsTopologicalSemiring F.residueField]
    [UniformSpace F.valuationSubring] [IsUniformAddGroup F.valuationSubring]
    [T2Space F.valuationSubring] [CompleteSpace F.valuationSubring]
    [IsTopologicalRing F.valuationSubring]
    [IsLinearTopology F.valuationSubring F.valuationSubring]
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) :
    F.residueField⟦X⟧ →+* F.valuationSubring :=
  PowerSeries.eval₂Hom hcoeff hπeval

/--
Establishes the identity `powerSeriesEvalSubringHom (F := F) p hcard π hcoeff hπeval
(PowerSeries.C a) = coeffSubringHom (F := F) p hcard a`.
-/
@[simp] theorem powerSeriesEvalSubringHom_C [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    [UniformSpace F.residueField] [IsUniformAddGroup F.residueField]
    [IsTopologicalSemiring F.residueField]
    [UniformSpace F.valuationSubring] [IsUniformAddGroup F.valuationSubring]
    [T2Space F.valuationSubring] [CompleteSpace F.valuationSubring]
    [IsTopologicalRing F.valuationSubring]
    [IsLinearTopology F.valuationSubring F.valuationSubring]
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) (a : F.residueField) :
    powerSeriesEvalSubringHom (F := F) p hcard π hcoeff hπeval
        (PowerSeries.C a) =
      coeffSubringHom (F := F) p hcard a := by
  have hfun :
      ⇑(PowerSeries.eval₂Hom hcoeff hπeval) =
        PowerSeries.eval₂ (coeffSubringHom (F := F) p hcard) π :=
    PowerSeries.coe_eval₂Hom hcoeff hπeval
  have happ := congrFun hfun (PowerSeries.C a)
  simpa [powerSeriesEvalSubringHom, PowerSeries.eval₂_C] using happ

/--
Establishes the identity `powerSeriesEvalSubringHom (F := F) p hcard π hcoeff hπeval PowerSeries.X
= π`.
-/
@[simp] theorem powerSeriesEvalSubringHom_X [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    [UniformSpace F.residueField] [IsUniformAddGroup F.residueField]
    [IsTopologicalSemiring F.residueField]
    [UniformSpace F.valuationSubring] [IsUniformAddGroup F.valuationSubring]
    [T2Space F.valuationSubring] [CompleteSpace F.valuationSubring]
    [IsTopologicalRing F.valuationSubring]
    [IsLinearTopology F.valuationSubring F.valuationSubring]
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) :
    powerSeriesEvalSubringHom (F := F) p hcard π hcoeff hπeval
        PowerSeries.X =
      π := by
  have hfun :
      ⇑(PowerSeries.eval₂Hom hcoeff hπeval) =
        PowerSeries.eval₂ (coeffSubringHom (F := F) p hcard) π :=
    PowerSeries.coe_eval₂Hom hcoeff hπeval
  have happ := congrFun hfun PowerSeries.X
  simpa [powerSeriesEvalSubringHom, PowerSeries.eval₂_X] using happ

/-- The valuation-ring evaluation composed with the inclusion `O_K -> K`. -/
noncomputable def powerSeriesEvalHom [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    [UniformSpace F.residueField] [IsUniformAddGroup F.residueField]
    [IsTopologicalSemiring F.residueField]
    [UniformSpace F.valuationSubring] [IsUniformAddGroup F.valuationSubring]
    [T2Space F.valuationSubring] [CompleteSpace F.valuationSubring]
    [IsTopologicalRing F.valuationSubring]
    [IsLinearTopology F.valuationSubring F.valuationSubring]
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) :
    F.residueField⟦X⟧ →+* K :=
  F.valuation.valuationSubring.subtype.comp
    (powerSeriesEvalSubringHom (F := F) p hcard π hcoeff hπeval)

/--
Establishes the identity `powerSeriesEvalHom (F := F) p hcard π hcoeff hπeval (PowerSeries.C a) =
coeffHom (F := F) p hcard a`.
-/
@[simp] theorem powerSeriesEvalHom_C [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    [UniformSpace F.residueField] [IsUniformAddGroup F.residueField]
    [IsTopologicalSemiring F.residueField]
    [UniformSpace F.valuationSubring] [IsUniformAddGroup F.valuationSubring]
    [T2Space F.valuationSubring] [CompleteSpace F.valuationSubring]
    [IsTopologicalRing F.valuationSubring]
    [IsLinearTopology F.valuationSubring F.valuationSubring]
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) (a : F.residueField) :
    powerSeriesEvalHom (F := F) p hcard π hcoeff hπeval
        (PowerSeries.C a) =
      coeffHom (F := F) p hcard a := by
  have hsub :=
    powerSeriesEvalSubringHom_C
      (F := F) p hcard π hcoeff hπeval a
  exact congrArg F.valuation.valuationSubring.subtype hsub

/--
Establishes the identity `powerSeriesEvalHom (F := F) p hcard π hcoeff hπeval PowerSeries.X = (π :
K)`.
-/
@[simp] theorem powerSeriesEvalHom_X [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    [UniformSpace F.residueField] [IsUniformAddGroup F.residueField]
    [IsTopologicalSemiring F.residueField]
    [UniformSpace F.valuationSubring] [IsUniformAddGroup F.valuationSubring]
    [T2Space F.valuationSubring] [CompleteSpace F.valuationSubring]
    [IsTopologicalRing F.valuationSubring]
    [IsLinearTopology F.valuationSubring F.valuationSubring]
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) :
    powerSeriesEvalHom (F := F) p hcard π hcoeff hπeval
        PowerSeries.X =
      (π : K) := by
  have hsub :=
    powerSeriesEvalSubringHom_X
      (F := F) p hcard π hcoeff hπeval
  exact congrArg F.valuation.valuationSubring.subtype hsub

/--
Proves that the specified element is a unit: `IsUnit (powerSeriesEvalHom (F := F) p hcard π hcoeff
hπeval PowerSeries.X)`.
-/
theorem powerSeriesEvalHom_X_isUnit [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.valuation.IsUniformizer (π : K))
    [UniformSpace F.residueField] [IsUniformAddGroup F.residueField]
    [IsTopologicalSemiring F.residueField]
    [UniformSpace F.valuationSubring] [IsUniformAddGroup F.valuationSubring]
    [T2Space F.valuationSubring] [CompleteSpace F.valuationSubring]
    [IsTopologicalRing F.valuationSubring]
    [IsLinearTopology F.valuationSubring F.valuationSubring]
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) :
    IsUnit
      (powerSeriesEvalHom (F := F) p hcard π hcoeff hπeval
        PowerSeries.X) := by
  simpa using
    (isUnit_iff_ne_zero.mpr hπ.ne_zero : IsUnit (π : K))

/-- The Laurent-series evaluation map `κ((X)) -> K` attached to the
Teichmuller coefficient field and the chosen uniformizer. -/
noncomputable def laurentSeriesEvalHom [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.valuation.IsUniformizer (π : K))
    [UniformSpace F.residueField] [IsUniformAddGroup F.residueField]
    [IsTopologicalSemiring F.residueField]
    [UniformSpace F.valuationSubring] [IsUniformAddGroup F.valuationSubring]
    [T2Space F.valuationSubring] [CompleteSpace F.valuationSubring]
    [IsTopologicalRing F.valuationSubring]
    [IsLinearTopology F.valuationSubring F.valuationSubring]
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) :
    F.residueField⸨X⸩ →+* K :=
  IsLocalization.Away.lift
    (S := F.residueField⸨X⸩)
    (P := K)
    (x := (PowerSeries.X : F.residueField⟦X⟧))
    (g := powerSeriesEvalHom (F := F) p hcard π hcoeff hπeval)
    (powerSeriesEvalHom_X_isUnit
      (F := F) p hcard π hπ hcoeff hπeval)

/--
Establishes the identity `(laurentSeriesEvalHom (F := F) p hcard π hπ hcoeff hπeval).comp
(algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩) = powerSeriesEvalHom (F := F) p hcard π hcoeff
hπeval`.
-/
theorem laurentSeriesEvalHom_comp_powerSeries [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.valuation.IsUniformizer (π : K))
    [UniformSpace F.residueField] [IsUniformAddGroup F.residueField]
    [IsTopologicalSemiring F.residueField]
    [UniformSpace F.valuationSubring] [IsUniformAddGroup F.valuationSubring]
    [T2Space F.valuationSubring] [CompleteSpace F.valuationSubring]
    [IsTopologicalRing F.valuationSubring]
    [IsLinearTopology F.valuationSubring F.valuationSubring]
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) :
    (laurentSeriesEvalHom (F := F) p hcard π hπ hcoeff hπeval).comp
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩) =
      powerSeriesEvalHom (F := F) p hcard π hcoeff hπeval := by
  exact
    IsLocalization.Away.lift_comp
      (S := F.residueField⸨X⸩)
      (P := K)
      (x := (PowerSeries.X : F.residueField⟦X⟧))
      (g := powerSeriesEvalHom (F := F) p hcard π hcoeff hπeval)
      (powerSeriesEvalHom_X_isUnit
        (F := F) p hcard π hπ hcoeff hπeval)

/--
Establishes the identity `laurentSeriesEvalHom (F := F) p hcard π hπ hcoeff hπeval (algebraMap
F.residueField⟦X⟧ F.residueField⸨X⸩ (PowerSeries.C a)) = coeffHom (F := F) p hcard a`.
-/
@[simp] theorem laurentSeriesEvalHom_algebraMap_C
    [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.valuation.IsUniformizer (π : K))
    [UniformSpace F.residueField] [IsUniformAddGroup F.residueField]
    [IsTopologicalSemiring F.residueField]
    [UniformSpace F.valuationSubring] [IsUniformAddGroup F.valuationSubring]
    [T2Space F.valuationSubring] [CompleteSpace F.valuationSubring]
    [IsTopologicalRing F.valuationSubring]
    [IsLinearTopology F.valuationSubring F.valuationSubring]
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) (a : F.residueField) :
    laurentSeriesEvalHom (F := F) p hcard π hπ hcoeff hπeval
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩
          (PowerSeries.C a)) =
      coeffHom (F := F) p hcard a := by
  change
    ((laurentSeriesEvalHom (F := F) p hcard π hπ hcoeff hπeval).comp
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩))
        (PowerSeries.C a) =
      coeffHom (F := F) p hcard a
  rw [laurentSeriesEvalHom_comp_powerSeries, powerSeriesEvalHom_C]

/--
Establishes the identity `laurentSeriesEvalHom (F := F) p hcard π hπ hcoeff hπeval (algebraMap
F.residueField⟦X⟧ F.residueField⸨X⸩ (PowerSeries.X : F.residueField⟦X⟧)) = (π : K)`.
-/
@[simp] theorem laurentSeriesEvalHom_algebraMap_X
    [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.valuation.IsUniformizer (π : K))
    [UniformSpace F.residueField] [IsUniformAddGroup F.residueField]
    [IsTopologicalSemiring F.residueField]
    [UniformSpace F.valuationSubring] [IsUniformAddGroup F.valuationSubring]
    [T2Space F.valuationSubring] [CompleteSpace F.valuationSubring]
    [IsTopologicalRing F.valuationSubring]
    [IsLinearTopology F.valuationSubring F.valuationSubring]
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) :
    laurentSeriesEvalHom (F := F) p hcard π hπ hcoeff hπeval
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩
          (PowerSeries.X : F.residueField⟦X⟧)) =
      (π : K) := by
  change
    ((laurentSeriesEvalHom (F := F) p hcard π hπ hcoeff hπeval).comp
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩))
        (PowerSeries.X : F.residueField⟦X⟧) =
      (π : K)
  rw [laurentSeriesEvalHom_comp_powerSeries, powerSeriesEvalHom_X]

/-- The algebra structure on `K` induced by the Laurent-series evaluation map.
This is the base algebra for the remaining finite-dimensionality step. -/
@[reducible] noncomputable def laurentSeriesAlgebra [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.valuation.IsUniformizer (π : K))
    [UniformSpace F.residueField] [IsUniformAddGroup F.residueField]
    [IsTopologicalSemiring F.residueField]
    [UniformSpace F.valuationSubring] [IsUniformAddGroup F.valuationSubring]
    [T2Space F.valuationSubring] [CompleteSpace F.valuationSubring]
    [IsTopologicalRing F.valuationSubring]
    [IsLinearTopology F.valuationSubring F.valuationSubring]
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) :
    Algebra F.residueField⸨X⸩ K :=
  RingHom.toAlgebra
    (laurentSeriesEvalHom (F := F) p hcard π hπ hcoeff hπeval)

/--
Under the Laurent-series algebra structure, the algebra map evaluates a series through
`laurentSeriesEvalHom`.
-/
theorem algebraMap_laurentSeriesAlgebra_apply
    [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.valuation.IsUniformizer (π : K))
    [UniformSpace F.residueField] [IsUniformAddGroup F.residueField]
    [IsTopologicalSemiring F.residueField]
    [UniformSpace F.valuationSubring] [IsUniformAddGroup F.valuationSubring]
    [T2Space F.valuationSubring] [CompleteSpace F.valuationSubring]
    [IsTopologicalRing F.valuationSubring]
    [IsLinearTopology F.valuationSubring F.valuationSubring]
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) (x : F.residueField⸨X⸩) :
    letI : Algebra F.residueField⸨X⸩ K :=
      laurentSeriesAlgebra
        (F := F) p hcard π hπ hcoeff hπeval
    algebraMap F.residueField⸨X⸩ K x =
      laurentSeriesEvalHom (F := F) p hcard π hπ hcoeff hπeval x := by
  rfl

/-- The adic valuation-ring power-series evaluation with all topology
instances supplied from the complete-DVF structure. -/
noncomputable def adicPowerSeriesEvalSubringHom
    [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.valuation.IsUniformizer (π : K)) :
    F.residueField⟦X⟧ →+* F.valuationSubring := by
  letI : UniformSpace F.residueField := ⊥
  haveI : DiscreteUniformity F.residueField := inferInstance
  haveI : IsUniformAddGroup F.residueField :=
    inferInstance
  letI : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
  haveI : IsLinearTopology F.valuationSubring F.valuationSubring :=
    valuationSubring_isLinearTopology_withIdeal (F := F)
  haveI : CompleteSpace F.valuationSubring :=
    valuationSubring_completeSpace_withIdeal (F := F)
  haveI : T2Space F.valuationSubring :=
    valuationSubring_t2Space_withIdeal (F := F)
  exact
    powerSeriesEvalSubringHom (F := F) p hcard π
      (continuous_coeffSubringHom_of_discrete (F := F) p hcard)
      (uniformizer_hasEval_valuationSubring_withIdeal (F := F) hπ)

/-- The `π`-adic power-series evaluation onto the valuation ring is
surjective.  This is the complete-DVR coefficient expansion, using the
Teichmuller representatives as digits. -/
theorem adicPowerSeriesEvalSubringHom_surjective
    [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.valuation.IsUniformizer (π : K)) :
    Function.Surjective
      (adicPowerSeriesEvalSubringHom (F := F) p hcard π hπ) := by
  let : UniformSpace F.residueField := ⊥
  have : DiscreteUniformity F.residueField := inferInstance
  have : IsUniformAddGroup F.residueField := inferInstance
  let : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
  have : IsLinearTopology F.valuationSubring F.valuationSubring :=
    valuationSubring_isLinearTopology_withIdeal (F := F)
  have : CompleteSpace F.valuationSubring :=
    valuationSubring_completeSpace_withIdeal (F := F)
  have : T2Space F.valuationSubring :=
    valuationSubring_t2Space_withIdeal (F := F)
  intro u
  let R := teichmullerRepresentativeSystem (F := F) p hcard
  let f : F.residueField⟦X⟧ :=
    PowerSeries.mk fun d =>
      F.residueMap
        (LubinTate.Valuations.remainder F R π hπ u d)
  let term : ℕ → F.valuationSubring := fun d =>
    coeffSubringHom (F := F) p hcard (PowerSeries.coeff d f) * π ^ d
  have hterm : ∀ d : ℕ,
      term d =
        LubinTate.Valuations.coeff F R π hπ u d * π ^ d := by
    intro d
    simp [term, f, R, teichmullerRepresentativeSystem,
      LubinTate.Valuations.coeff]
  have hpartial : ∀ N : ℕ,
      (∑ d ∈ Finset.range N, term d) =
        LubinTate.Valuations.partialSum F R π hπ u N := by
    intro N
    induction N with
    | zero =>
        simp [term, LubinTate.Valuations.partialSum]
    | succ N ih =>
        rw [Finset.sum_range_succ, ih, hterm N]
        simp [LubinTate.Valuations.partialSum]
  have hhas :
      HasSum term
        (PowerSeries.eval₂ (coeffSubringHom (F := F) p hcard) π f) := by
    simpa [term] using
      PowerSeries.hasSum_eval₂
        (continuous_coeffSubringHom_of_discrete (F := F) p hcard)
        (uniformizer_hasEval_valuationSubring_withIdeal (F := F) hπ) f
  have htend_eval :
      Filter.Tendsto
        (fun N => LubinTate.Valuations.partialSum F R π hπ u N)
        Filter.atTop
        (nhds (PowerSeries.eval₂ (coeffSubringHom (F := F) p hcard) π f)) := by
    exact hhas.tendsto_sum_nat.congr'
      (Filter.Eventually.of_forall fun N => hpartial N)
  have htend_u :
      Filter.Tendsto
        (fun N => LubinTate.Valuations.partialSum F R π hπ u N)
        Filter.atTop (nhds u) := by
    have hwrapped :=
      LubinTate.Valuations.partialSum_tendsto_adic F R π hπ u
    have hunderlying :=
      WithTopology.tendsto_nhds_iff.mp hwrapped
    simpa [R] using hunderlying
  have heval_eq_u :
      PowerSeries.eval₂ (coeffSubringHom (F := F) p hcard) π f = u :=
    tendsto_nhds_unique htend_eval htend_u
  have hevalHom_eq_u :
      (PowerSeries.eval₂Hom
        (continuous_coeffSubringHom_of_discrete (F := F) p hcard)
        (uniformizer_hasEval_valuationSubring_withIdeal (F := F) hπ)) f = u := by
    have hfun :=
      PowerSeries.coe_eval₂Hom
        (continuous_coeffSubringHom_of_discrete (F := F) p hcard)
        (uniformizer_hasEval_valuationSubring_withIdeal (F := F) hπ)
    rw [congrFun hfun f]
    exact heval_eq_u
  refine ⟨f, ?_⟩
  simpa [adicPowerSeriesEvalSubringHom, powerSeriesEvalSubringHom] using
    hevalHom_eq_u

/-- The adic Laurent-series evaluation with all topology instances supplied
from the complete-DVF structure. -/
noncomputable def adicLaurentSeriesEvalHom
    [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.valuation.IsUniformizer (π : K)) :
    F.residueField⸨X⸩ →+* K := by
  letI : UniformSpace F.residueField := ⊥
  haveI : DiscreteUniformity F.residueField := inferInstance
  haveI : IsUniformAddGroup F.residueField :=
    inferInstance
  letI : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
  haveI : IsLinearTopology F.valuationSubring F.valuationSubring :=
    valuationSubring_isLinearTopology_withIdeal (F := F)
  haveI : CompleteSpace F.valuationSubring :=
    valuationSubring_completeSpace_withIdeal (F := F)
  haveI : T2Space F.valuationSubring :=
    valuationSubring_t2Space_withIdeal (F := F)
  exact
    laurentSeriesEvalHom (F := F) p hcard π hπ
      (continuous_coeffSubringHom_of_discrete (F := F) p hcard)
      (uniformizer_hasEval_valuationSubring_withIdeal (F := F) hπ)

/--
Establishes the identity `adicLaurentSeriesEvalHom (F := F) p hcard π hπ (algebraMap
F.residueField⟦X⟧ F.residueField⸨X⸩ (PowerSeries.C a)) = coeffHom (F := F) p hcard a`.
-/
@[simp] theorem adicLaurentSeriesEvalHom_algebraMap_C
    [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.valuation.IsUniformizer (π : K)) (a : F.residueField) :
    adicLaurentSeriesEvalHom (F := F) p hcard π hπ
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩
          (PowerSeries.C a)) =
      coeffHom (F := F) p hcard a := by
  let : UniformSpace F.residueField := ⊥
  have : DiscreteUniformity F.residueField := inferInstance
  have : IsUniformAddGroup F.residueField :=
    inferInstance
  let : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
  have : IsLinearTopology F.valuationSubring F.valuationSubring :=
    valuationSubring_isLinearTopology_withIdeal (F := F)
  have : CompleteSpace F.valuationSubring :=
    valuationSubring_completeSpace_withIdeal (F := F)
  have : T2Space F.valuationSubring :=
    valuationSubring_t2Space_withIdeal (F := F)
  simpa [adicLaurentSeriesEvalHom] using
    laurentSeriesEvalHom_algebraMap_C
      (F := F) p hcard π hπ
      (continuous_coeffSubringHom_of_discrete (F := F) p hcard)
      (uniformizer_hasEval_valuationSubring_withIdeal (F := F) hπ) a

/--
Establishes the identity `adicLaurentSeriesEvalHom (F := F) p hcard π hπ (algebraMap
F.residueField⟦X⟧ F.residueField⸨X⸩ (PowerSeries.X : F.residueField⟦X⟧)) = (π : K)`.
-/
@[simp] theorem adicLaurentSeriesEvalHom_algebraMap_X
    [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.valuation.IsUniformizer (π : K)) :
    adicLaurentSeriesEvalHom (F := F) p hcard π hπ
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩
          (PowerSeries.X : F.residueField⟦X⟧)) =
      (π : K) := by
  let : UniformSpace F.residueField := ⊥
  have : DiscreteUniformity F.residueField := inferInstance
  have : IsUniformAddGroup F.residueField :=
    inferInstance
  let : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
  have : IsLinearTopology F.valuationSubring F.valuationSubring :=
    valuationSubring_isLinearTopology_withIdeal (F := F)
  have : CompleteSpace F.valuationSubring :=
    valuationSubring_completeSpace_withIdeal (F := F)
  have : T2Space F.valuationSubring :=
    valuationSubring_t2Space_withIdeal (F := F)
  simpa [adicLaurentSeriesEvalHom] using
    laurentSeriesEvalHom_algebraMap_X
      (F := F) p hcard π hπ
      (continuous_coeffSubringHom_of_discrete (F := F) p hcard)
      (uniformizer_hasEval_valuationSubring_withIdeal (F := F) hπ)

/--
Establishes the identity `(adicLaurentSeriesEvalHom (F := F) p hcard π hπ).comp (algebraMap
F.residueField⟦X⟧ F.residueField⸨X⸩) = F.valuation.valuationSubring.subtype.comp
(adicPowerSeriesEvalSubringHom (F := F) p hcard π hπ)`.
-/
theorem adicLaurentSeriesEvalHom_comp_powerSeries
    [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.valuation.IsUniformizer (π : K)) :
    (adicLaurentSeriesEvalHom (F := F) p hcard π hπ).comp
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩) =
      F.valuation.valuationSubring.subtype.comp
        (adicPowerSeriesEvalSubringHom (F := F) p hcard π hπ) := by
  let : UniformSpace F.residueField := ⊥
  have : DiscreteUniformity F.residueField := inferInstance
  have : IsUniformAddGroup F.residueField := inferInstance
  let : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
  have : IsLinearTopology F.valuationSubring F.valuationSubring :=
    valuationSubring_isLinearTopology_withIdeal (F := F)
  have : CompleteSpace F.valuationSubring :=
    valuationSubring_completeSpace_withIdeal (F := F)
  have : T2Space F.valuationSubring :=
    valuationSubring_t2Space_withIdeal (F := F)
  simpa [adicLaurentSeriesEvalHom, adicPowerSeriesEvalSubringHom,
    powerSeriesEvalHom] using
    laurentSeriesEvalHom_comp_powerSeries
      (F := F) p hcard π hπ
      (continuous_coeffSubringHom_of_discrete (F := F) p hcard)
      (uniformizer_hasEval_valuationSubring_withIdeal (F := F) hπ)

/-- The equal-characteristic Laurent-series evaluation is onto the field. -/
theorem adicLaurentSeriesEvalHom_surjective
    [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.valuation.IsUniformizer (π : K)) :
    Function.Surjective
      (adicLaurentSeriesEvalHom (F := F) p hcard π hπ) := by
  intro x
  by_cases hx : x = 0
  · refine ⟨0, ?_⟩
    simp [hx]
  rcases LubinTate.Valuations.exists_laurent_unit F π hπ hx with
    ⟨m, u, _hu, hx_eq⟩
  rcases adicPowerSeriesEvalSubringHom_surjective
      (F := F) p hcard π hπ u with
    ⟨f, hf⟩
  let Xls : F.residueField⸨X⸩ :=
    algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩
      (PowerSeries.X : F.residueField⟦X⟧)
  let y : F.residueField⸨X⸩ :=
    Xls ^ m *
      algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩ f
  refine ⟨y, ?_⟩
  have hcomp :=
    congrFun
      (congrArg DFunLike.coe
        (adicLaurentSeriesEvalHom_comp_powerSeries
          (F := F) p hcard π hπ)) f
  have hX :
      adicLaurentSeriesEvalHom (F := F) p hcard π hπ Xls = (π : K) := by
    simpa [Xls] using
      adicLaurentSeriesEvalHom_algebraMap_X
        (F := F) p hcard π hπ
  have hpow :
      adicLaurentSeriesEvalHom (F := F) p hcard π hπ (Xls ^ m) =
        (π : K) ^ m := by
    rw [map_zpow₀, hX]
  have halg :
      adicLaurentSeriesEvalHom (F := F) p hcard π hπ
          (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩ f) =
        (u : K) := by
    exact hcomp.trans (congrArg F.valuation.valuationSubring.subtype hf)
  calc
    adicLaurentSeriesEvalHom (F := F) p hcard π hπ y
        =
          (π : K) ^ m * (u : K) := by
            change
              adicLaurentSeriesEvalHom (F := F) p hcard π hπ
                  (Xls ^ m *
                    algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩ f) =
                (π : K) ^ m * (u : K)
            rw [map_mul, hpow, halg]
    _ = x := hx_eq.symm

end EqualCharacteristicLaurent
end CompleteDVF

/-- If the structure map of an algebra over a field is onto, the algebra is
one-dimensional as a vector space over the base. -/
theorem finiteDimensional_of_surjective_algebraMap
    (E L : Type u) [Field E] [Field L] [Algebra E L]
    (hsurj : Function.Surjective (algebraMap E L)) :
    FiniteDimensional E L := by
  exact
    FiniteDimensional.of_surjective (Algebra.linearMap E L) <| by
      simpa [Algebra.coe_linearMap] using hsurj

namespace LocalField

open scoped PowerSeries LaurentSeries Filter Topology BigOperators

variable {K : Type u} [Field K]
variable (F : LocalField.{u, v} K)

/-- The image in `K` of the equal-characteristic Laurent-series evaluation.
This is the candidate base field for the converse direction of the local-field structure classification. -/
noncomputable def laurentImageSubfield
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    Subfield K :=
  (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom
    (F := F.toCompleteDVF) p hcard π hπ).fieldRange

/--
Establishes the membership statement
`CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom (F := F.toCompleteDVF) p hcard π
hπ x ∈ F.laurentImageSubfield p hcard π hπ`.
-/
theorem adicLaurentSeriesEval_mem_laurentImageSubfield
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (x : F.residueField⸨X⸩) :
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom
        (F := F.toCompleteDVF) p hcard π hπ x ∈
      F.laurentImageSubfield p hcard π hπ :=
  RingHom.mem_fieldRange_self
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom
      (F := F.toCompleteDVF) p hcard π hπ) x

/-- Establishes the identity `F.laurentImageSubfield p hcard π hπ = ⊤`. -/
theorem laurentImageSubfield_eq_top
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    F.laurentImageSubfield p hcard π hπ = ⊤ := by
  ext x
  constructor
  · intro _hx
    trivial
  · intro _hx
    rcases _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom_surjective
        (F := F.toCompleteDVF) p hcard π hπ x with
      ⟨y, hy⟩
    exact (RingHom.mem_fieldRange).2 ⟨y, hy⟩

/-- The Laurent-series field is identified with its image in `K`. -/
noncomputable def laurentSeriesEquivLaurentImageSubfield
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    F.residueField⸨X⸩ ≃+*
      F.laurentImageSubfield p hcard π hπ :=
  RingHom.rangeRestrictFieldEquiv
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom
      (F := F.toCompleteDVF) p hcard π hπ)

/--
Establishes the identity `((F.laurentSeriesEquivLaurentImageSubfield p hcard π hπ x :
F.laurentImageSubfield p hcard π hπ) : K) =
CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom (F := F.toCompleteDVF) p hcard π
hπ x`.
-/
@[simp] theorem laurentSeriesEquivLaurentImageSubfield_apply_coe
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (x : F.residueField⸨X⸩) :
    ((F.laurentSeriesEquivLaurentImageSubfield p hcard π hπ x :
        F.laurentImageSubfield p hcard π hπ) : K) =
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom
        (F := F.toCompleteDVF) p hcard π hπ x := by
  rfl

/--
Establishes the identity `((F.laurentSeriesEquivLaurentImageSubfield p hcard π hπ (algebraMap
F.residueField⟦X⟧ F.residueField⸨X⸩ (PowerSeries.C a)) : F.laurentImageSubfield p hcard π hπ) : K)
= CompleteDVF.EqualCharacteristicLaurent.coeffHom (F := F.toCompleteDVF) p hcard a`.
-/
@[simp] theorem laurentSeriesEquivLaurentImageSubfield_algebraMap_C
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (a : F.residueField) :
    ((F.laurentSeriesEquivLaurentImageSubfield p hcard π hπ
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩
          (PowerSeries.C a)) :
        F.laurentImageSubfield p hcard π hπ) : K) =
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom
        (F := F.toCompleteDVF) p hcard a := by
  simpa using
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom_algebraMap_C
      (F := F.toCompleteDVF) p hcard π hπ a

/--
Establishes the identity `((F.laurentSeriesEquivLaurentImageSubfield p hcard π hπ (algebraMap
F.residueField⟦X⟧ F.residueField⸨X⸩ (PowerSeries.X : F.residueField⟦X⟧)) : F.laurentImageSubfield
p hcard π hπ) : K) = (π : K)`.
-/
@[simp] theorem laurentSeriesEquivLaurentImageSubfield_algebraMap_X
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    ((F.laurentSeriesEquivLaurentImageSubfield p hcard π hπ
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩
          (PowerSeries.X : F.residueField⟦X⟧)) :
        F.laurentImageSubfield p hcard π hπ) : K) =
      (π : K) := by
  simpa using
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom_algebraMap_X
      (F := F.toCompleteDVF) p hcard π hπ

/-- The image base field is nontrivially normed by the norm induced from the
range-restricted valuation topology on `K`. -/
@[implicit_reducible]
noncomputable def laurentImageSubfield_nontriviallyNormedField
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    letI : Valued K
        (MonoidHom.mrange F.toCompleteDVF.valuation.toMonoidWithZeroHom) :=
      ((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF))
    letI : NontriviallyNormedField K :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
    NontriviallyNormedField
      (F.laurentImageSubfield p hcard π hπ) := by
  let Γ : Type v :=
    MonoidHom.mrange F.toCompleteDVF.valuation.toMonoidWithZeroHom
  letI : Valued K Γ := ((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF))
  haveI : (Valued.v : _root_.Valuation K Γ).RankOne := by
    change
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict
        F.toCompleteDVF).RankOne
    exact
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_rankOne
        F.toCompleteDVF
  letI : NontriviallyNormedField K :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
  let piSub : F.laurentImageSubfield p hcard π hπ :=
    F.laurentSeriesEquivLaurentImageSubfield p hcard π hπ
      (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩
        (PowerSeries.X : F.residueField⟦X⟧))
  have hpiSub_coe : (piSub : K) = (π : K) := by
    simpa [piSub] using
      F.laurentSeriesEquivLaurentImageSubfield_algebraMap_X
        p hcard π hπ
  refine NontriviallyNormedField.ofNormNeOne ?_
  refine ⟨piSub, ?_, ?_⟩
  · intro hzero
    have hzeroK : (piSub : K) = 0 := by
      simpa using congrArg Subtype.val hzero
    rw [hpiSub_coe] at hzeroK
    exact hπ.ne_zero hzeroK
  · have hπ_lt_one :
        _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F.toCompleteDVF (π : K) < 1 := by
      rw [← Subtype.coe_lt_coe]
      simpa [Γ, _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply] using hπ.val_lt_one
    have hπ_norm_lt_one_K : ‖(π : K)‖ < 1 := by
      simpa [_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued] using
        (Valued.toNormedField.norm_lt_one_iff
          (x := (π : K))).2 hπ_lt_one
    have hπ_norm_lt_one : ‖piSub‖ < 1 := by
      change ‖(piSub : K)‖ < 1
      simpa [hpiSub_coe] using hπ_norm_lt_one_K
    exact ne_of_lt hπ_norm_lt_one

/-- The ambient local field is a normed algebra over the Laurent image base. -/
@[implicit_reducible]
noncomputable def laurentImageSubfield_normedAlgebra
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    letI : Valued K
        (MonoidHom.mrange F.toCompleteDVF.valuation.toMonoidWithZeroHom) :=
      ((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF))
    letI : NontriviallyNormedField K :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
    letI : NontriviallyNormedField
        (F.laurentImageSubfield p hcard π hπ) :=
      F.laurentImageSubfield_nontriviallyNormedField p hcard π hπ
    NormedAlgebra (F.laurentImageSubfield p hcard π hπ) K := by
  let Γ : Type v :=
    MonoidHom.mrange F.toCompleteDVF.valuation.toMonoidWithZeroHom
  letI : Valued K Γ := ((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF))
  letI : NontriviallyNormedField K :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
  letI : NontriviallyNormedField
      (F.laurentImageSubfield p hcard π hπ) :=
    F.laurentImageSubfield_nontriviallyNormedField p hcard π hπ
  exact
    { (inferInstance :
        Algebra (F.laurentImageSubfield p hcard π hπ) K) with
      norm_smul_le := fun a x => by
        change ‖(a : K) * x‖ ≤ ‖(a : K)‖ * ‖x‖
        exact norm_mul_le (a : K) x }

/-- The local field is finite-dimensional over the image of the Laurent-series
base field. -/
theorem finiteDimensional_over_laurentImageSubfield
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    letI : Valued K
        (MonoidHom.mrange F.toCompleteDVF.valuation.toMonoidWithZeroHom) :=
      ((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF))
    letI : NontriviallyNormedField K :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
    letI : NontriviallyNormedField
        (F.laurentImageSubfield p hcard π hπ) :=
      F.laurentImageSubfield_nontriviallyNormedField p hcard π hπ
    letI : NormedAlgebra
        (F.laurentImageSubfield p hcard π hπ) K :=
      F.laurentImageSubfield_normedAlgebra p hcard π hπ
    FiniteDimensional (F.laurentImageSubfield p hcard π hπ) K := by
  let Γ : Type v :=
    MonoidHom.mrange F.toCompleteDVF.valuation.toMonoidWithZeroHom
  let : Valued K Γ := ((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF))
  let : NontriviallyNormedField K :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
  let : NontriviallyNormedField
      (F.laurentImageSubfield p hcard π hπ) :=
    F.laurentImageSubfield_nontriviallyNormedField p hcard π hπ
  let : NormedAlgebra
      (F.laurentImageSubfield p hcard π hπ) K :=
    F.laurentImageSubfield_normedAlgebra p hcard π hπ
  have htop : F.laurentImageSubfield p hcard π hπ = ⊤ :=
    F.laurentImageSubfield_eq_top p hcard π hπ
  have hsurj :
      Function.Surjective
        (algebraMap (F.laurentImageSubfield p hcard π hπ) K) := by
    intro x
    have hxmem : x ∈ F.laurentImageSubfield p hcard π hπ := by
      rw [htop]
      trivial
    exact ⟨⟨x, hxmem⟩, rfl⟩
  exact
    finiteDimensional_of_surjective_algebraMap
      (F.laurentImageSubfield p hcard π hπ) K hsurj

/-- The actual Laurent-series base acts on `K` through the image subfield. -/
@[reducible] noncomputable def laurentSeriesAlgebra
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    Algebra F.residueField⸨X⸩ K :=
  RingHom.toAlgebra
    ((F.laurentImageSubfield p hcard π hπ).subtype.comp
      (F.laurentSeriesEquivLaurentImageSubfield p hcard π hπ :
        F.residueField⸨X⸩ →+*
          F.laurentImageSubfield p hcard π hπ))

/--
The Laurent-series algebra map is the series equivalence followed by inclusion of the Laurent
image subfield.
-/
theorem laurentSeriesAlgebra_algebraMap
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    letI : Algebra F.residueField⸨X⸩ K :=
      F.laurentSeriesAlgebra p hcard π hπ
    algebraMap F.residueField⸨X⸩ K =
      (F.laurentImageSubfield p hcard π hπ).subtype.comp
        (F.laurentSeriesEquivLaurentImageSubfield p hcard π hπ :
          F.residueField⸨X⸩ →+*
            F.laurentImageSubfield p hcard π hπ) := by
  rfl

/-- The local field is finite-dimensional over the actual Laurent-series
base field. -/
theorem finiteDimensional_over_laurentSeries
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    letI : Algebra F.residueField⸨X⸩ K :=
      F.laurentSeriesAlgebra p hcard π hπ
    FiniteDimensional F.residueField⸨X⸩ K := by
  let : Algebra F.residueField⸨X⸩ K :=
    F.laurentSeriesAlgebra p hcard π hπ
  let Γ : Type v :=
    MonoidHom.mrange F.toCompleteDVF.valuation.toMonoidWithZeroHom
  let : Valued K Γ := ((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF))
  let : NontriviallyNormedField K :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
  let : NontriviallyNormedField
      (F.laurentImageSubfield p hcard π hπ) :=
    F.laurentImageSubfield_nontriviallyNormedField p hcard π hπ
  let : NormedAlgebra
      (F.laurentImageSubfield p hcard π hπ) K :=
    F.laurentImageSubfield_normedAlgebra p hcard π hπ
  have : FiniteDimensional
      (F.laurentImageSubfield p hcard π hπ) K :=
    F.finiteDimensional_over_laurentImageSubfield p hcard π hπ
  have hcompat :
      (algebraMap (F.laurentImageSubfield p hcard π hπ) K).comp
          (F.laurentSeriesEquivLaurentImageSubfield p hcard π hπ :
            F.residueField⸨X⸩ →+*
              F.laurentImageSubfield p hcard π hπ) =
        (RingEquiv.refl K).toRingHom.comp
          (algebraMap F.residueField⸨X⸩ K) := by
    ext x
    rfl
  have hrank :
      Module.rank F.residueField⸨X⸩ K =
        Module.rank (F.laurentImageSubfield p hcard π hπ) K := by
    simpa using
      (Algebra.rank_eq_of_equiv_equiv
        (F.laurentSeriesEquivLaurentImageSubfield p hcard π hπ)
        (RingEquiv.refl K) hcompat)
  exact
    FiniteDimensional.of_rank_eq_nat
      (n := Module.finrank
        (F.laurentImageSubfield p hcard π hπ) K) <| by
        simpa [Module.finrank_eq_rank'] using hrank

/-- The local-field structure classification, equal-characteristic converse branch: after choosing a
uniformizer and the finite residue field as coefficient field, `K` is
finite-dimensional over `κ((X))`. -/
theorem equalCharacteristic_exists_laurent_finiteExtension
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ)) :
    ∃ π : F.valuationSubring,
      ∃ _hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K),
        ∃ hAlg : Algebra F.residueField⸨X⸩ K,
          letI : Algebra F.residueField⸨X⸩ K := hAlg
          FiniteDimensional F.residueField⸨X⸩ K := by
  rcases F.exists_uniformizer with ⟨π, hπ⟩
  exact
    ⟨π, hπ, F.laurentSeriesAlgebra p hcard π hπ,
      F.finiteDimensional_over_laurentSeries p hcard π hπ⟩

end LocalField
end LocalFieldTheory.DiscreteValuationField
