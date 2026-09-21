/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Topology.AdicCompletionInverseLimit
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core
/-!
# The canonical p-adic action on first principal units

This file constructs the common source used in both cases of LubinTate,
The field-unit structure theorem.  A first principal unit is recovered from its
classes in the level quotients `U^1 / U^(n+1)`.  For a local field these
quotients are finite and have exponent dividing `p^(f*n)`, where the residue
field has cardinality `p^f`.
Reduction of a p-adic integer modulo these powers therefore acts on every
finite coordinate, and compatibility of reduction transports the action to
`U^1`.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace CompleteDVF
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
namespace higherPrincipalUnitGroup

open LubinTate
open LubinTate.Valuations

variable {K : Type u} [Field K]

/-- A fixed uniformizer used only to invoke the direct quotient form of
the adic inverse-limit equivalence.  The resulting p-adic action is characterized below by its
ordinary integral powers. -/
noncomputable def chosenPrincipalUnitPadicUniformizer
    (F : CompleteDVF.{u, v} K) : F.valuationSubring :=
  Classical.choose F.exists_uniformizer

/-- The chosen principal-unit parameter has valuation one and is a uniformizer. -/
theorem chosenPrincipalUnitPadicUniformizer_isUniformizer
    (F : CompleteDVF.{u, v} K) :
    F.valuation.IsUniformizer (chosenPrincipalUnitPadicUniformizer F : K) :=
  Classical.choose_spec F.exists_uniformizer

/-- The chosen valuation-ring uniformizer is irreducible. -/
theorem chosenPrincipalUnitPadicUniformizer_irreducible
    (F : CompleteDVF.{u, v} K) :
    Irreducible (chosenPrincipalUnitPadicUniformizer F) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  exact F.maximalIdeal_eq_span_uniformizer
    (chosenPrincipalUnitPadicUniformizer_isUniformizer F)

/-- For the chosen uniformizer, the higher-unit subgroup `1 + pi^n O` is the
intrinsic `n`-th higher principal-unit group. -/
theorem higherUnitSubgroup_chosenPrincipalUnitPadicUniformizer
    (F : CompleteDVF.{u, v} K) (n : ℕ) :
    higherUnitSubgroup (chosenPrincipalUnitPadicUniformizer F) n =
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) n := by
  ext x
  rw [mem_higherUnitSubgroup_iff_sub_one_mem_powerIdeal,
    higherPrincipalUnitGroup.mem_iff]
  have hideal :
      uniformizerPowerIdeal (chosenPrincipalUnitPadicUniformizer F) n =
        F.maximalIdeal ^ n := by
    calc
      uniformizerPowerIdeal (chosenPrincipalUnitPadicUniformizer F) n =
        (uniformizerPowerIdeal (chosenPrincipalUnitPadicUniformizer F) 1) ^ n :=
        (dvrPowerIdeal_one_pow _ n).symm
      _ = F.maximalIdeal ^ n := by
        rw [uniformizerPowerIdeal, pow_one,
          ← F.maximalIdeal_eq_span_uniformizer
            (chosenPrincipalUnitPadicUniformizer_isUniformizer F)]
  rw [hideal]

/-- Transition on the intrinsic quotients `O^*/U^(n+1)`. -/
def Internal.higherUnitQuotientTransition
    (F : CompleteDVF.{u, v} K) {m n : ℕ} (hmn : m ≤ n) :
    F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n + 1) →*
      F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (m + 1) :=
  (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).quotient_principalUnitSubgroup_mapOfLe
    (Nat.succ_le_succ hmn)

/-- The intrinsic full unit inverse limit `lim O^*/U^(n+1)`. -/
abbrev Internal.higherUnitInverseLimitCarrier
    (F : CompleteDVF.{u, v} K) : Type u :=
  compatibleGroupFamilies
    (fun n : ℕ =>
      F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n + 1))
    (fun {_ _} hmn => Internal.higherUnitQuotientTransition F hmn)

open Internal

/-- Changing from the uniformizer presentation of a level quotient to the
intrinsic principal-unit presentation. -/
noncomputable def Internal.uniformizerHigherUnitQuotientEquiv
    (F : CompleteDVF.{u, v} K) (n : ℕ) :
    F.valuationSubringˣ ⧸
        higherUnitSubgroup (chosenPrincipalUnitPadicUniformizer F) (n + 1) ≃*
      F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n + 1) :=
  QuotientGroup.quotientMulEquivOfEq
    (higherUnitSubgroup_chosenPrincipalUnitPadicUniformizer F (n + 1))

/--
Establishes the identity `uniformizerHigherUnitQuotientEquiv F n (QuotientGroup.mk x) =
QuotientGroup.mk x`.
-/
@[simp] theorem Internal.uniformizerHigherUnitQuotientEquiv_mk
    (F : CompleteDVF.{u, v} K) (n : ℕ) (x : F.valuationSubringˣ) :
    uniformizerHigherUnitQuotientEquiv F n (QuotientGroup.mk x) =
      QuotientGroup.mk x := by
  exact QuotientGroup.quotientMulEquivOfEq_mk _ x

/-- The uniformizer and intrinsic presentations give the same full inverse
limit. -/
noncomputable def Internal.uniformizerHigherUnitInverseLimitEquiv
    (F : CompleteDVF.{u, v} K) :
    dvrHigherUnitQuotientInverseLimit
        (chosenPrincipalUnitPadicUniformizer F) ≃*
      Internal.higherUnitInverseLimitCarrier F :=
  (dvrHigherUnitQuotientInverseLimitRepresentation
      (chosenPrincipalUnitPadicUniformizer F)).trans
    (compatibleGroupFamiliesMulEquiv
      (fun n : ℕ =>
        F.valuationSubringˣ ⧸
          higherUnitSubgroup (chosenPrincipalUnitPadicUniformizer F) (n + 1))
      (fun n : ℕ =>
        F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n + 1))
      (fun {_ _} hmn =>
        dvrHigherUnitQuotientTransition
          (chosenPrincipalUnitPadicUniformizer F) hmn)
      (fun {_ _} hmn => higherUnitQuotientTransition F hmn)
      (uniformizerHigherUnitQuotientEquiv F)
      (by
        intro m n hmn q
        refine QuotientGroup.induction_on q ?_
        intro x
        rw [uniformizerHigherUnitQuotientEquiv_mk]
        change QuotientGroup.mk x = QuotientGroup.mk x
        rfl))

/-- The direct quotient isomorphism of the adic inverse-limit equivalence, rewritten using the
intrinsic higher principal-unit filtration. -/
noncomputable def Internal.unitsEquivHigherUnitQuotientInverseLimit
    (F : CompleteDVF.{u, v} K) :
    F.valuationSubringˣ ≃* Internal.higherUnitInverseLimitCarrier F := by
  let pi := chosenPrincipalUnitPadicUniformizer F
  have hpi : Irreducible pi := chosenPrincipalUnitPadicUniformizer_irreducible F
  letI : IsAdicComplete (uniformizerPowerIdeal pi 1) F.valuationSubring := by
    have hmax : uniformizerPowerIdeal pi 1 = F.maximalIdeal := by
      rw [uniformizerPowerIdeal, pow_one,
        ← F.maximalIdeal_eq_span_uniformizer
          (chosenPrincipalUnitPadicUniformizer_isUniformizer F)]
    rw [hmax]
    exact ValuationTheory.DiscreteValuationField.Valuation.isAdicComplete F.valuation
  exact
    (dvrUnitsEquivHigherUnitQuotientInverseLimit hpi).trans
      (uniformizerHigherUnitInverseLimitEquiv F)

/--
The defining evaluation formula for `Internal.unitsEquivHigherUnitQuotientInverseLimit` is
`(unitsEquivHigherUnitQuotientInverseLimit F x).1 n = QuotientGroup.mk x`.
-/
theorem Internal.unitsEquivHigherUnitQuotientInverseLimit_apply
    (F : CompleteDVF.{u, v} K) (x : F.valuationSubringˣ) (n : ℕ) :
    (unitsEquivHigherUnitQuotientInverseLimit F x).1 n =
      QuotientGroup.mk x := by
  let pi := chosenPrincipalUnitPadicUniformizer F
  have hpi : Irreducible pi := chosenPrincipalUnitPadicUniformizer_irreducible F
  let : IsAdicComplete (uniformizerPowerIdeal pi 1) F.valuationSubring := by
    have hmax : uniformizerPowerIdeal pi 1 = F.maximalIdeal := by
      rw [uniformizerPowerIdeal, pow_one,
        ← F.maximalIdeal_eq_span_uniformizer
          (chosenPrincipalUnitPadicUniformizer_isUniformizer F)]
    rw [hmax]
    exact ValuationTheory.DiscreteValuationField.Valuation.isAdicComplete F.valuation
  change
    uniformizerHigherUnitQuotientEquiv F n
        (dvrHigherUnitQuotientInverseLimit_eval pi n
          (dvrUnitsEquivHigherUnitQuotientInverseLimit hpi x)) =
      QuotientGroup.mk x
  rw [dvrUnitsEquivHigherUnitQuotientInverseLimit_apply,
    uniformizerHigherUnitQuotientEquiv_mk]

/-- The change from the uniformizer presentation of the full unit inverse
limit to the intrinsic presentation is a homeomorphism when all quotient
coordinates are discrete. -/
noncomputable def Internal.uniformizerHigherUnitInverseLimitHomeomorphIntrinsic
    (F : CompleteDVF.{u, v} K) :
    letI : (n : ℕ) → TopologicalSpace
        (F.valuationSubringˣ ⧸
          higherUnitSubgroup (chosenPrincipalUnitPadicUniformizer F) (n + 1)) :=
      fun _ => ⊥
    letI : (n : ℕ) → TopologicalSpace
        (F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n + 1)) :=
      fun _ => ⊥
    dvrHigherUnitQuotientInverseLimit
        (chosenPrincipalUnitPadicUniformizer F) ≃ₜ
      Internal.higherUnitInverseLimitCarrier F := by
  letI : (n : ℕ) → TopologicalSpace
      (F.valuationSubringˣ ⧸
        higherUnitSubgroup (chosenPrincipalUnitPadicUniformizer F) (n + 1)) :=
    fun _ => ⊥
  letI : (n : ℕ) → TopologicalSpace
      (F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n + 1)) :=
    fun _ => ⊥
  letI : (n : ℕ) → DiscreteTopology
      (F.valuationSubringˣ ⧸
        higherUnitSubgroup (chosenPrincipalUnitPadicUniformizer F) (n + 1)) :=
    fun _ => ⟨rfl⟩
  letI : (n : ℕ) → DiscreteTopology
      (F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n + 1)) :=
    fun _ => ⟨rfl⟩
  let e := uniformizerHigherUnitInverseLimitEquiv F
  refine
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · change Continuous fun x => e x
    exact Continuous.subtype_mk
      (continuous_pi fun n => by
        change Continuous fun x :
            dvrHigherUnitQuotientInverseLimit
              (chosenPrincipalUnitPadicUniformizer F) =>
          uniformizerHigherUnitQuotientEquiv F n
            (dvrHigherUnitQuotientInverseLimit_eval
              (chosenPrincipalUnitPadicUniformizer F) n x)
        have heval : Continuous fun x :
            dvrHigherUnitQuotientInverseLimit
              (chosenPrincipalUnitPadicUniformizer F) =>
            dvrHigherUnitQuotientInverseLimit_eval
              (chosenPrincipalUnitPadicUniformizer F) n x :=
          (DiscreteHigherUnitQuotient.homeomorph
            (chosenPrincipalUnitPadicUniformizer F) (n + 1)).continuous.comp
            (dvrHigherUnitQuotientInverseLimit_discreteEval_continuous
              (chosenPrincipalUnitPadicUniformizer F) n)
        exact continuous_of_discreteTopology.comp heval)
      (fun x : dvrHigherUnitQuotientInverseLimit
          (chosenPrincipalUnitPadicUniformizer F) => by
        intro i j hij
        show higherUnitQuotientTransition F hij
            (uniformizerHigherUnitQuotientEquiv F j
              (dvrHigherUnitQuotientInverseLimit_eval
                (chosenPrincipalUnitPadicUniformizer F) j x)) =
          uniformizerHigherUnitQuotientEquiv F i
            (dvrHigherUnitQuotientInverseLimit_eval
              (chosenPrincipalUnitPadicUniformizer F) i x)
        exact (e x).2 hij)
  · change Continuous fun x => e.symm x
    apply (dvrHigherUnitQuotientInverseLimit_continuous_iff
      (chosenPrincipalUnitPadicUniformizer F) (fun x => e.symm x)).2
    intro n
    change Continuous fun x : Internal.higherUnitInverseLimitCarrier F =>
      DiscreteHigherUnitQuotient.of
        (chosenPrincipalUnitPadicUniformizer F) (n + 1)
        ((uniformizerHigherUnitQuotientEquiv F n).symm (x.1 n))
    exact
      (DiscreteHigherUnitQuotient.homeomorph
        (chosenPrincipalUnitPadicUniformizer F) (n + 1)).symm.continuous.comp
        (continuous_of_discreteTopology.comp
          ((continuous_apply n).comp continuous_subtype_val))

/-- Topological full-unit form of the adic inverse-limit equivalence, rewritten intrinsically. -/
noncomputable def Internal.unitsHomeomorphHigherUnitQuotientInverseLimit
    (F : CompleteDVF.{u, v} K) :
    letI : TopologicalSpace F.valuationSubring :=
      (uniformizerPowerIdeal (chosenPrincipalUnitPadicUniformizer F) 1).adicTopology
    letI : (n : ℕ) → TopologicalSpace
        (F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n + 1)) :=
      fun _ => ⊥
    F.valuationSubringˣ ≃ₜ Internal.higherUnitInverseLimitCarrier F := by
  let pi := chosenPrincipalUnitPadicUniformizer F
  letI : TopologicalSpace F.valuationSubring :=
    (uniformizerPowerIdeal pi 1).adicTopology
  letI : (n : ℕ) → TopologicalSpace
      (F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n + 1)) :=
    fun _ => ⊥
  letI : (n : ℕ) → TopologicalSpace
      (F.valuationSubringˣ ⧸ higherUnitSubgroup pi (n + 1)) :=
    fun _ => ⊥
  have hpi : Irreducible pi := chosenPrincipalUnitPadicUniformizer_irreducible F
  letI : IsAdicComplete (uniformizerPowerIdeal pi 1) F.valuationSubring := by
    have hmax : uniformizerPowerIdeal pi 1 = F.maximalIdeal := by
      rw [uniformizerPowerIdeal, pow_one,
        ← F.maximalIdeal_eq_span_uniformizer
          (chosenPrincipalUnitPadicUniformizer_isUniformizer F)]
    rw [hmax]
    exact ValuationTheory.DiscreteValuationField.Valuation.isAdicComplete F.valuation
  exact
    (WithTopology.homeomorph
      (α := F.valuationSubringˣ)
      (topology := adicUnitsTopology (uniformizerPowerIdeal pi 1))).symm.trans
      ((unitsEquivHigherUnitQuotientInverseLimitHomeomorph hpi).trans
        (Internal.uniformizerHigherUnitInverseLimitHomeomorphIntrinsic F))

/--
The unit-to-inverse-limit homeomorphism sends a unit to its canonical class at every higher-unit
quotient level.
-/
theorem Internal.unitsHomeomorphHigherUnitQuotientInverseLimit_apply
    (F : CompleteDVF.{u, v} K) (x : F.valuationSubringˣ) (n : ℕ) :
    letI : TopologicalSpace F.valuationSubring :=
      (uniformizerPowerIdeal (chosenPrincipalUnitPadicUniformizer F) 1).adicTopology
    letI : (n : ℕ) → TopologicalSpace
        (F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n + 1)) :=
      fun _ => ⊥
    (Internal.unitsHomeomorphHigherUnitQuotientInverseLimit F x).1 n =
      QuotientGroup.mk x := by
  let pi := chosenPrincipalUnitPadicUniformizer F
  let : TopologicalSpace F.valuationSubring :=
    (uniformizerPowerIdeal pi 1).adicTopology
  let : (n : ℕ) → TopologicalSpace
      (F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n + 1)) :=
    fun _ => ⊥
  let : (n : ℕ) → TopologicalSpace
      (F.valuationSubringˣ ⧸ higherUnitSubgroup pi (n + 1)) :=
    fun _ => ⊥
  have hpi : Irreducible pi := chosenPrincipalUnitPadicUniformizer_irreducible F
  let : IsAdicComplete (uniformizerPowerIdeal pi 1) F.valuationSubring := by
    have hmax : uniformizerPowerIdeal pi 1 = F.maximalIdeal := by
      rw [uniformizerPowerIdeal, pow_one,
        ← F.maximalIdeal_eq_span_uniformizer
          (chosenPrincipalUnitPadicUniformizer_isUniformizer F)]
    rw [hmax]
    exact ValuationTheory.DiscreteValuationField.Valuation.isAdicComplete F.valuation
  change uniformizerHigherUnitQuotientEquiv F n
      (dvrHigherUnitQuotientInverseLimit_eval pi n
        (unitsEquivHigherUnitQuotientInverseLimitHomeomorph
          hpi
          (WithTopology.toTopology (adicUnitsTopology (uniformizerPowerIdeal pi 1)) x))) =
    QuotientGroup.mk x
  change uniformizerHigherUnitQuotientEquiv F n (QuotientGroup.mk x) =
    QuotientGroup.mk x
  exact uniformizerHigherUnitQuotientEquiv_mk F n x

/-! ## Restriction of the adic inverse-limit equivalence to first principal units -/

/-- The raw carrier of the `n`-th coordinate `U^1/U^(n+1)`. -/
abbrev Internal.principalUnitQuotientCarrier
    (F : CompleteDVF.{u, v} K) (n : ℕ) : Type u :=
  (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotient
    1 (n + 1)

/-- Transition `U^1/U^(n+1) -> U^1/U^(m+1)` for `m <= n`. -/
def Internal.principalUnitQuotientCarrierTransition
    (F : CompleteDVF.{u, v} K) {m n : ℕ} (hmn : m ≤ n) :
    Internal.principalUnitQuotientCarrier F n →*
      Internal.principalUnitQuotientCarrier F m := by
  let U := higherPrincipalUnitGroup.toPrincipalUnitFiltration F
  change U.principalUnitSubquotient 1 (n + 1) →*
    U.principalUnitSubquotient 1 (m + 1)
  refine U.principalUnitSubquotientLift 1 (n + 1)
    (U.principalUnitSubquotientMk 1 (m + 1)) ?_
  intro x hx
  rw [MonoidHom.mem_ker,
    U.principalUnitSubquotient_mk_eq_one_iff]
  change (x : F.valuationSubringˣ) ∈
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F)
      (m + 1)
  exact higherPrincipalUnitGroup.antitone F (Nat.succ_le_succ hmn) hx

/--
Establishes the identity `principalUnitQuotientCarrierTransition F hmn
((higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientMk 1 (n + 1) x) =
(higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientMk 1 (m + 1) x`.
-/
@[simp] theorem Internal.principalUnitQuotientCarrierTransition_mk
    (F : CompleteDVF.{u, v} K) {m n : ℕ} (hmn : m ≤ n)
    (x : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) :
    principalUnitQuotientCarrierTransition F hmn
        ((higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientMk
          1 (n + 1) x) =
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientMk
        1 (m + 1) x :=
  rfl

/-- The projective limit `lim_n U^1/U^(n+1)`. -/
abbrev Internal.principalUnitInverseLimitCarrier
    (F : CompleteDVF.{u, v} K) : Type u :=
  compatibleGroupFamilies
    (Internal.principalUnitQuotientCarrier F)
    (fun {_ _} hmn => principalUnitQuotientCarrierTransition F hmn)

/-- Evaluation of a principal-unit compatible family at level `n`. -/
def Internal.principalUnitInverseLimitCarrierEval
    (F : CompleteDVF.{u, v} K) (n : ℕ) :
    Internal.principalUnitInverseLimitCarrier F →*
      Internal.principalUnitQuotientCarrier F n :=
  compatibleGroupFamiliesEval
    (Internal.principalUnitQuotientCarrier F)
    (fun {_ _} hmn => principalUnitQuotientCarrierTransition F hmn) n

/--
The defining evaluation formula for `Internal.principalUnitInverseLimitCarrierEval` is
`principalUnitInverseLimitCarrierEval F n x = x.1 n`.
-/
@[simp]
theorem Internal.principalUnitInverseLimitCarrierEval_apply
    (F : CompleteDVF.{u, v} K) (n : ℕ)
    (x : Internal.principalUnitInverseLimitCarrier F) :
    principalUnitInverseLimitCarrierEval F n x = x.1 n :=
  rfl

/-- Named compatibility law for a principal-unit inverse-limit family. -/
theorem Internal.principalUnitInverseLimitCarrier_compatible
    (F : CompleteDVF.{u, v} K)
    (x : Internal.principalUnitInverseLimitCarrier F)
    {m n : ℕ} (hmn : m ≤ n) :
    principalUnitQuotientCarrierTransition F hmn
        (principalUnitInverseLimitCarrierEval F n x) =
      principalUnitInverseLimitCarrierEval F m x :=
  compatibleGroupFamilies_transition
    (Internal.principalUnitQuotientCarrier F)
    (fun {_ _} hij => principalUnitQuotientCarrierTransition F hij) x hmn

/-- Principal-unit inverse-limit families are determined by their
coordinates. -/
@[ext]
theorem Internal.principalUnitInverseLimitCarrier_ext
    (F : CompleteDVF.{u, v} K)
    {x y : Internal.principalUnitInverseLimitCarrier F}
    (h : ∀ n, principalUnitInverseLimitCarrierEval F n x =
      principalUnitInverseLimitCarrierEval F n y) : x = y :=
  compatibleGroupFamilies_ext
    (Internal.principalUnitQuotientCarrier F)
    (fun {_ _} hij => principalUnitQuotientCarrierTransition F hij) h
end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
