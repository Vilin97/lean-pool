/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.Homomorphisms
/-!
# Extending the logarithm to the field-unit group

The logarithm on first principal units does not extend by killing a chosen
uniformizer.  Its uniformizer value must instead be chosen so that the
distinguished rational prime has logarithm zero.  This file isolates that
algebraic construction.
-/

noncomputable section

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- Extend a homomorphism on first principal units to the three factors in
the uniformizer–residue–principal-unit decomposition, killing the residue-root factor and assigning the additive
value `c` to one power of the chosen uniformizer. -/
noncomputable def fieldUnitDecompositionLogHomWithUniformizerValue
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A) :
    CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F →*
      Multiplicative A where
  toFun z :=
    φ z.1.2 * Multiplicative.ofAdd (Multiplicative.toAdd z.2 • c)
  map_one' := by simp
  map_mul' z w := by
    apply Multiplicative.toAdd.injective
    change
      Multiplicative.toAdd (φ (z.1.2 * w.1.2)) +
          (Multiplicative.toAdd z.2 + Multiplicative.toAdd w.2) • c =
        (Multiplicative.toAdd (φ z.1.2) + Multiplicative.toAdd z.2 • c) +
          (Multiplicative.toAdd (φ w.1.2) + Multiplicative.toAdd w.2 • c)
    rw [φ.map_mul]
    simp only [toAdd_mul, add_zsmul]
    abel

/--
The defining evaluation formula for `fieldUnitDecompositionLogHomWithUniformizerValue` is
`fieldUnitDecompositionLogHomWithUniformizerValue F φ c z = φ z.1.2 * Multiplicative.ofAdd
(Multiplicative.toAdd z.2 • c)`.
-/
@[simp] theorem fieldUnitDecompositionLogHomWithUniformizerValue_apply
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A)
    (z : CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F) :
    fieldUnitDecompositionLogHomWithUniformizerValue F φ c z =
      φ z.1.2 * Multiplicative.ofAdd (Multiplicative.toAdd z.2 • c) :=
  rfl

/--
Establishes the identity `fieldUnitDecompositionLogHomWithUniformizerValue F φ c ((ζ, 1), (1 :
Multiplicative ℤ)) = 1`.
-/
@[simp] theorem fieldUnitDecompositionLogHomWithUniformizerValue_root
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A)
    (ζ : CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
    fieldUnitDecompositionLogHomWithUniformizerValue F φ c
        ((ζ, 1), (1 : Multiplicative ℤ)) = 1 := by
  simp

/--
Establishes the identity `fieldUnitDecompositionLogHomWithUniformizerValue F φ c (((1 :
CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F), u), (1 : Multiplicative ℤ)) = φ
u`.
-/
@[simp] theorem fieldUnitDecompositionLogHomWithUniformizerValue_principal
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A)
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) :
    fieldUnitDecompositionLogHomWithUniformizerValue F φ c
        (((1 : CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F), u),
          (1 : Multiplicative ℤ)) = φ u := by
  simp

/--
Establishes the identity `fieldUnitDecompositionLogHomWithUniformizerValue F φ c (((1 :
CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F), (1 :
(CompleteDVF.higherPrincipalUnitGroup F) 1)), Multiplicative.ofAdd m) = Multiplicative.ofAdd (m •
c)`.
-/
@[simp] theorem fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A)
    (m : ℤ) :
    fieldUnitDecompositionLogHomWithUniformizerValue F φ c
        (((1 : CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F),
            (1 : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)),
          Multiplicative.ofAdd m) = Multiplicative.ofAdd (m • c) := by
  simp

/-- Transport the corrected factor logarithm across a chosen the uniformizer–residue–principal-unit decomposition
decomposition of the field-unit group. -/
noncomputable def fieldUnitLogHomWithUniformizerValue
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (d : CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃* Kˣ)
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A) :
    Kˣ →* Multiplicative A :=
  (fieldUnitDecompositionLogHomWithUniformizerValue F φ c).comp
    d.symm.toMonoidHom

/--
The defining evaluation formula for `fieldUnitLogHomWithUniformizerValue` is
`fieldUnitLogHomWithUniformizerValue F d φ c x = φ (d.symm x).1.2 * Multiplicative.ofAdd
(Multiplicative.toAdd (d.symm x).2 • c)`.
-/
@[simp] theorem fieldUnitLogHomWithUniformizerValue_apply
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (d : CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃* Kˣ)
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A) (x : Kˣ) :
    fieldUnitLogHomWithUniformizerValue F d φ c x =
      φ (d.symm x).1.2 *
        Multiplicative.ofAdd (Multiplicative.toAdd (d.symm x).2 • c) :=
  rfl

/--
Establishes the identity `fieldUnitLogHomWithUniformizerValue F d φ c x = φ z.1.2 *
Multiplicative.ofAdd (Multiplicative.toAdd z.2 • c)`.
-/
theorem fieldUnitLogHomWithUniformizerValue_apply_of_decomposition_eq
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (d : CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃* Kˣ)
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A)
    (z : CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F)
    {x : Kˣ} (hx : d z = x) :
    fieldUnitLogHomWithUniformizerValue F d φ c x =
      φ z.1.2 * Multiplicative.ofAdd (Multiplicative.toAdd z.2 • c) := by
  subst x
  simp

/-- Establishes the identity `fieldUnitLogHomWithUniformizerValue F d φ c x = φ u`. -/
theorem fieldUnitLogHomWithUniformizerValue_eq_of_principal_decomposition
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (d : CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃* Kˣ)
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A)
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) {x : Kˣ}
    (hx :
      d (((1 : CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F), u),
          (1 : Multiplicative ℤ)) = x) :
    fieldUnitLogHomWithUniformizerValue F d φ c x = φ u := by
  simpa using
    fieldUnitLogHomWithUniformizerValue_apply_of_decomposition_eq
      F d φ c
      (((1 : CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F), u),
        (1 : Multiplicative ℤ)) hx

/-- On first principal units, the corrected field logarithm agrees with the
given principal-unit logarithm, for the decomposition supplied by a chosen
uniformizer. -/
theorem fieldUnitLogHomWithUniformizerValue_eq_of_completeDVF_principal
    (F : CompleteDVF K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A)
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) :
    fieldUnitLogHomWithUniformizerValue F
        (CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
          F hπ) φ c
        (CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (u : F.valuationSubringˣ)) = φ u := by
  apply fieldUnitLogHomWithUniformizerValue_eq_of_principal_decomposition
    (F := F)
    (d :=
      CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
        F hπ)
    (φ := φ) (c := c) (u := u)
  simp [CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply]

/-- Continuity of the corrected logarithm on the three decomposition factors.
The uniformizer coordinate is discrete, while continuity on the principal-unit
coordinate is exactly the supplied continuity of `φ`. -/
theorem continuous_fieldUnitDecompositionLogHomWithUniformizerValue
    [TopologicalSpace K] (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A)
    (hφ : Continuous φ) :
    Continuous (fieldUnitDecompositionLogHomWithUniformizerValue F φ c) := by
  have hprincipal :
      Continuous
        (fun z :
            CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F =>
          φ z.1.2) :=
    hφ.comp (continuous_snd.comp continuous_fst)
  have huniformizer :
      Continuous
        (fun z :
            CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F =>
          Multiplicative.ofAdd (Multiplicative.toAdd z.2 • c)) := by
    have hdisc :
        Continuous
          (fun m : Multiplicative ℤ =>
            Multiplicative.ofAdd (Multiplicative.toAdd m • c)) :=
      continuous_of_discreteTopology
    exact hdisc.comp continuous_snd
  exact hprincipal.mul huniformizer

/-- Continuity after transporting the corrected factor logarithm across the
topological decomposition from the uniformizer–residue–principal-unit decomposition. -/
theorem continuous_fieldUnitLogHomWithUniformizerValue
    [TopologicalSpace K] (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A]
    (d : CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃ₜ* Kˣ)
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A)
    (hφ : Continuous φ) :
    Continuous (fieldUnitLogHomWithUniformizerValue F d.toMulEquiv φ c) := by
  exact
    (continuous_fieldUnitDecompositionLogHomWithUniformizerValue F φ c hφ).comp
      d.symm.continuous

/-- The uniformizer value forced by the requirement that a distinguished
field unit `a` have logarithm zero.  The nonzero-exponent condition needed for
that conclusion is stated separately. -/
noncomputable def uniformizerLogValueKilling
    (F : CompleteDVF K) [Finite F.residueField] [CharZero K]
    (d : CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃* Kˣ)
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative K) (a : Kˣ) : K :=
  -(((Multiplicative.toAdd (d.symm a).2 : ℤ) : K)⁻¹ *
      Multiplicative.toAdd (φ (d.symm a).1.2))

/-- With the forced uniformizer value, the distinguished field unit is sent
to zero (written as `1` in `Multiplicative K`) whenever its uniformizer
exponent is nonzero. -/
theorem fieldUnitLogHomWithUniformizerValue_uniformizerLogValueKilling
    (F : CompleteDVF K) [Finite F.residueField] [CharZero K]
    (d : CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃* Kˣ)
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative K) (a : Kˣ)
    (ha : Multiplicative.toAdd (d.symm a).2 ≠ 0) :
    fieldUnitLogHomWithUniformizerValue F d φ
        (uniformizerLogValueKilling F d φ a) a = 1 := by
  apply Multiplicative.toAdd.injective
  change
    Multiplicative.toAdd (φ (d.symm a).1.2) +
        Multiplicative.toAdd (d.symm a).2 •
          uniformizerLogValueKilling F d φ a = 0
  rw [uniformizerLogValueKilling]
  simp [zsmul_eq_mul, ha]

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField
