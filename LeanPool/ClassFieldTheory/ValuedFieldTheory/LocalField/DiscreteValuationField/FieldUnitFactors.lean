/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.ContinuousFieldUnitLog
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Topology.Instances.ZMod
/-!
# Finite and uniformizer factors of the field-unit group

This file isolates the two factors of the field-unit structure theorem which do not depend on
the structure theorem for first principal units.  The Teichmuller factor is
the cyclic group of order `q - 1`, with its (necessarily discrete) topology.
-/

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  fieldUnitDecompositionFactors →
    fieldUnitDecompositionFactors

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  residueRootsOfUnityEquivResidueFieldUnits →
    residueRootsOfUnityEquivResidueFieldUnits

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  residueRootsOfUnityGroup →
    residueRootsOfUnityGroup


noncomputable section

universe u v

namespace LocalFieldTheory.DiscreteValuationField
namespace CompleteDVF
namespace higherPrincipalUnitGroup

variable {K : Type u} [Field K]

/-- A continuous algebraic equivalence from a compact group to a Hausdorff
group is automatically a topological group equivalence. -/
noncomputable def continuousMulEquivOfCompactToT2
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [Mul A] [Mul B] [CompactSpace A] [T2Space B]
    (e : A ≃* B) (he : Continuous e) : A ≃ₜ* B :=
  ContinuousMulEquiv.mk'
    (he.homeoOfEquivCompactToT2 (f := e.toEquiv)) e.map_mul

/-- Additive version of `continuousMulEquivOfCompactToT2`. -/
noncomputable def continuousAddEquivOfCompactToT2
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [Add A] [Add B] [CompactSpace A] [T2Space B]
    (e : A ≃+ B) (he : Continuous e) : A ≃ₜ+ B :=
  ContinuousAddEquiv.mk'
    (he.homeoOfEquivCompactToT2 (f := e.toEquiv)) e.map_add

/-- Product of two topological multiplicative equivalences. -/
noncomputable def continuousMulEquivProdCongr
    {A B C D : Type*}
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace D]
    [MulOneClass A] [MulOneClass B] [MulOneClass C] [MulOneClass D]
    (e : A ≃ₜ* B) (f : C ≃ₜ* D) : A × C ≃ₜ* B × D :=
  { e.toMulEquiv.prodCongr f.toMulEquiv with
    continuous_toFun := by
      change Continuous (fun x : A × C => (e x.1, f x.2))
      fun_prop
    continuous_invFun := by
      change Continuous (fun x : B × D => (e.symm x.1, f.symm x.2))
      fun_prop }

/-- Swapping two factors is a topological multiplicative equivalence. -/
noncomputable def continuousMulEquivProdComm
    (A B : Type*) [TopologicalSpace A] [TopologicalSpace B]
    [MulOneClass A] [MulOneClass B] : A × B ≃ₜ* B × A :=
  { (MulEquiv.prodComm : A × B ≃* B × A) with
    continuous_toFun := by
      change Continuous (fun x : A × B => (x.2, x.1))
      fun_prop
    continuous_invFun := by
      change Continuous (fun x : B × A => (x.2, x.1))
      fun_prop }

/-- The Teichmuller roots form, algebraically and topologically, the cyclic
group of order `q - 1`, where `q` is the residue-field cardinality. -/
noncomputable def residueRootsOfUnityContinuousMulEquivZMod
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField] :
    letI : Valued K (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F
    Multiplicative (ZMod (Nat.card F.residueField - 1)) ≃ₜ*
      residueRootsOfUnityGroup F := by
  letI : Valued K (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F
  rw [← Nat.card_units F.residueField]
  let e : Multiplicative (ZMod (Nat.card F.residueFieldˣ)) ≃*
      residueRootsOfUnityGroup F :=
    (zmodCyclicMulEquiv
      (G := F.residueFieldˣ) (inferInstance : IsCyclic F.residueFieldˣ)).trans
      (residueRootsOfUnityEquivResidueFieldUnits F).symm
  haveI : Finite
    (residueRootsOfUnityGroup F) :=
    Finite.of_equiv F.residueFieldˣ
      (residueRootsOfUnityEquivResidueFieldUnits F).symm.toEquiv
  exact
    { e with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- The field-unit structure theorem with the still-to-be-classified first-principal-unit
factor left visible: the other two factors are already the standard cyclic
factors appearing in the decomposition. -/
noncomputable def fieldUnitsContinuousMulEquivCyclicRootsPrincipalUnitsUniformizer
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K)) :
    letI : Valued K (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F
    ((Multiplicative (ZMod (Nat.card F.residueField - 1)) ×
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F 1) ×
          Multiplicative ℤ) ≃ₜ* Kˣ := by
  letI : Valued K (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F
  exact
    (continuousMulEquivProdCongr
      (continuousMulEquivProdCongr
        (residueRootsOfUnityContinuousMulEquivZMod F)
        (ContinuousMulEquiv.refl
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F 1)))
      (ContinuousMulEquiv.refl (Multiplicative ℤ))).trans
      (fieldUnitsContinuousMulEquivRootsPrincipalUnitsUniformizerOfCompleteDVFMrangeRestrict
        F hπ)

/-- The uniformizer–residue–principal-unit decomposition in the topology carried directly by a
standard
`ℤᵐ⁰`-valued valuation.  This is the decomposition used to assemble the two
cases of the field-unit structure theorem. -/
noncomputable def fieldUnitsContinuousMulEquivRootsPrincipalUnitsUniformizerOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)]
    {π : (MultiplicativeIntegerValuation.completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K)) :
    let F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} K :=
      MultiplicativeIntegerValuation.completeDVFOfWithZeroValuation v
    letI : Finite F.residueField := by
      change Finite (IsLocalRing.ResidueField v.valuationSubring)
      infer_instance
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    fieldUnitDecompositionFactors F ≃ₜ* Kˣ := by
  let F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} K :=
    MultiplicativeIntegerValuation.completeDVFOfWithZeroValuation v
  let direct : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let restricted : Valued K
      (MonoidHom.mrange v.toMonoidWithZeroHom) :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F
  have huniform :
      (Valued.mk' v).toUniformSpace =
        (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued
          F).toUniformSpace := by
    change (Valued.mk' v).toUniformSpace =
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued
        (WithZeroValuationTopology.completeDVF v)).toUniformSpace
    exact WithZeroValuationTopology.valuedMk_uniformSpace_eq_mrangeRestrict v
  haveI : Finite F.residueField := by
    change Finite (IsLocalRing.ResidueField v.valuationSubring)
    infer_instance
  let E :=
    letI : Valued K
        (MonoidHom.mrange v.toMonoidWithZeroHom) := restricted
    fieldUnitsContinuousMulEquivRootsPrincipalUnitsUniformizerOfCompleteDVFMrangeRestrict
      F hπ
  have htop : direct.toTopologicalSpace = restricted.toTopologicalSpace := by
    exact congrArg (fun U : UniformSpace K => U.toTopologicalSpace) huniform
  let unitsTopology (t : TopologicalSpace K) : TopologicalSpace Kˣ :=
    letI : TopologicalSpace K := t
    inferInstance
  let factorsTopology (t : TopologicalSpace K) :
      TopologicalSpace
        (fieldUnitDecompositionFactors
          F) :=
    letI : TopologicalSpace K := t
    inferInstance
  have hdom :
      factorsTopology direct.toTopologicalSpace =
        factorsTopology restricted.toTopologicalSpace :=
    congrArg factorsTopology htop
  have hcod :
      unitsTopology direct.toTopologicalSpace =
        unitsTopology restricted.toTopologicalSpace :=
    congrArg unitsTopology htop
  let e := E.toMulEquiv
  have heContinuous :
      @Continuous
        (fieldUnitDecompositionFactors
          F)
        Kˣ
        (factorsTopology restricted.toTopologicalSpace)
        (unitsTopology restricted.toTopologicalSpace) e := by
    exact E.continuous
  have heSymmContinuous :
      @Continuous
        Kˣ
        (fieldUnitDecompositionFactors
          F)
        (unitsTopology restricted.toTopologicalSpace)
        (factorsTopology restricted.toTopologicalSpace) e.symm := by
    exact E.symm.continuous
  letI : Valued K (WithZero (Multiplicative ℤ)) := direct
  exact
    { e with
      continuous_toFun := by
        change @Continuous
          (fieldUnitDecompositionFactors
            F)
          Kˣ
          (factorsTopology direct.toTopologicalSpace)
          (unitsTopology direct.toTopologicalSpace) e
        rw [hdom, hcod]
        exact heContinuous
      continuous_invFun := by
        change @Continuous
          Kˣ
          (fieldUnitDecompositionFactors
            F)
          (unitsTopology direct.toTopologicalSpace)
          (factorsTopology direct.toTopologicalSpace) e.symm
        rw [hdom, hcod]
        exact heSymmContinuous }

/-- The Teichmuller root factor in the direct topology of a standard
`ℤᵐ⁰`-valued valuation. -/
noncomputable def residueRootsOfUnityContinuousMulEquivZModOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] :
    let F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} K :=
      MultiplicativeIntegerValuation.completeDVFOfWithZeroValuation v
    letI : Finite F.residueField := by
      change Finite (IsLocalRing.ResidueField v.valuationSubring)
      infer_instance
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Multiplicative (ZMod (Nat.card F.residueField - 1)) ≃ₜ*
      residueRootsOfUnityGroup F := by
  let F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} K :=
    MultiplicativeIntegerValuation.completeDVFOfWithZeroValuation v
  haveI : Finite F.residueField := by
    change Finite (IsLocalRing.ResidueField v.valuationSubring)
    infer_instance
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  change Multiplicative (ZMod (Nat.card F.residueField - 1)) ≃ₜ*
    residueRootsOfUnityGroup F
  rw [← Nat.card_units F.residueField]
  let e : Multiplicative (ZMod (Nat.card F.residueFieldˣ)) ≃*
      residueRootsOfUnityGroup F :=
    (zmodCyclicMulEquiv
      (G := F.residueFieldˣ) (inferInstance : IsCyclic F.residueFieldˣ)).trans
      (residueRootsOfUnityEquivResidueFieldUnits F).symm
  haveI : Finite
    (residueRootsOfUnityGroup F) :=
    Finite.of_equiv F.residueFieldˣ
      (residueRootsOfUnityEquivResidueFieldUnits F).symm.toEquiv
  exact
    { e with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- The field-unit structure theorem with the principal-unit factor left visible, now in the
direct standard valuation topology. -/
noncomputable def
  fieldUnitsContinuousMulEquivCyclicRootsPrincipalUnitsUniformizerOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)]
    {π : (MultiplicativeIntegerValuation.completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K)) :
    let F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} K :=
      MultiplicativeIntegerValuation.completeDVFOfWithZeroValuation v
    letI : Finite F.residueField := by
      change Finite (IsLocalRing.ResidueField v.valuationSubring)
      infer_instance
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    ((Multiplicative (ZMod (Nat.card F.residueField - 1)) ×
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F 1) ×
          Multiplicative ℤ) ≃ₜ* Kˣ := by
  let F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} K :=
    MultiplicativeIntegerValuation.completeDVFOfWithZeroValuation v
  haveI : Finite F.residueField := by
    change Finite (IsLocalRing.ResidueField v.valuationSubring)
    infer_instance
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  exact
    (continuousMulEquivProdCongr
      (continuousMulEquivProdCongr
        (residueRootsOfUnityContinuousMulEquivZModOfWithZeroValuation v)
        (ContinuousMulEquiv.refl
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F 1)))
      (ContinuousMulEquiv.refl (Multiplicative ℤ))).trans
      (fieldUnitsContinuousMulEquivRootsPrincipalUnitsUniformizerOfWithZeroValuation
        v hπ)

/-- Assemble the field-unit structure theorem from a topological classification of `U^1`,
with the factors ordered canonically as: uniformizer, Teichmuller
roots, then principal units. -/
noncomputable def fieldUnitsContinuousMulEquivUniformizerRootsPrincipalUnitsOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)]
    {π : (MultiplicativeIntegerValuation.completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (P : Type*) [TopologicalSpace P] [MulOneClass P] :
    let F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} K :=
      MultiplicativeIntegerValuation.completeDVFOfWithZeroValuation v
    letI : Finite F.residueField := by
      change Finite (IsLocalRing.ResidueField v.valuationSubring)
      infer_instance
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    (P ≃ₜ* LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F 1) →
      Multiplicative ℤ ×
        (Multiplicative (ZMod (Nat.card F.residueField - 1)) × P) ≃ₜ* Kˣ := by
  let F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} K :=
    MultiplicativeIntegerValuation.completeDVFOfWithZeroValuation v
  haveI : Finite F.residueField := by
    change Finite (IsLocalRing.ResidueField v.valuationSubring)
    infer_instance
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  change (P ≃ₜ* LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F 1) →
    Multiplicative ℤ ×
      (Multiplicative (ZMod (Nat.card F.residueField - 1)) × P) ≃ₜ* Kˣ
  intro eP
  exact
    (continuousMulEquivProdComm (Multiplicative ℤ)
      (Multiplicative (ZMod (Nat.card F.residueField - 1)) × P)).trans
      ((continuousMulEquivProdCongr
        (continuousMulEquivProdCongr
          (ContinuousMulEquiv.refl
            (Multiplicative (ZMod (Nat.card F.residueField - 1)))) eP)
        (ContinuousMulEquiv.refl (Multiplicative ℤ))).trans
        (fieldUnitsContinuousMulEquivCyclicRootsPrincipalUnitsUniformizerOfWithZeroValuation
          v hπ))

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
