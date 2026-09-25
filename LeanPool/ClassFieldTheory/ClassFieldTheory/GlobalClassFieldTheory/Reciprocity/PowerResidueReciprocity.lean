/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.FinitePlaceCharacterComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteIdeleArtin
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.HilbertProductFormula
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.PowerResidueSymbols.Ideal
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.FinitePlaces
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.QuadraticReciprocity
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Rational
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Kummer.PowerResidueTameFormula
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.ExtensionInvariants
public import LeanPool.ClassFieldTheory.ClassFieldTheory.KummerTheory.Concrete.SimpleExtensionLocalBehavior
public import LeanPool.ClassFieldTheory.ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.FiniteRadicalSupport
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.CyclotomicNorm.PrincipalUnits
/-!
# Bad-place support and correction for power-residue reciprocity

For two global units `a` and `b`, the local Kummer factor can be nontrivial
only where `a`, `b`, or the exponent fails to be a valuation-ring unit.  This
file records that concrete finite set, proves triviality outside it from the
unramified simple-Kummer criterion and the local norm kernel, and constructs
the exponent-place and infinite-place correction in the common field-valued
group of roots of unity.
-/

@[expose] public section

open scoped BigOperators NumberField NumberTheorySymbols ValuativeRel WithZero
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open KummerTheory
open AlgebraicNumberTheory.PowerResidueSymbols
open LocalClassFieldTheory.Kummer
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (K : Type) [Field K] [NumberField K]

open scoped Classical in
/-- Equality for the valuation used to define a valuative relation transports
to equality in the relation's canonical value group. -/
private theorem canonicalValuation_eq_of_valuation_eq
    {R Γ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation R Γ) (x y : R) (hxy : v x = v y) :
    letI : ValuativeRel R := ValuativeRel.ofValuation v
    ValuativeRel.valuation R x = ValuativeRel.valuation R y := by
  let : ValuativeRel R := ValuativeRel.ofValuation v
  change
    ValuativeRel.ValueGroupWithZero.mk x 1 =
      ValuativeRel.ValueGroupWithZero.mk y 1
  rw [ValuativeRel.ValueGroupWithZero.mk_eq_mk]
  constructor
  · change v (x * (1 : R)) ≤ v (y * (1 : R))
    simpa only [mul_one] using hxy.le
  · change v (y * (1 : R)) ≤ v (x * (1 : R))
    simpa only [mul_one] using hxy.ge

open scoped Classical in
/-- The bounded-natural-number form of nonarchimedeanness for a finite-place
absolute value.  Naming this bridge keeps all completion residue constructions
on one proof-irrelevant provider. -/
private theorem finitePlaceAdicAbv_nonarchimedeanAbsoluteValue
    (v : HeightOneSpectrum (𝓞 K)) :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue
      (HeightOneSpectrum.adicAbv K v) :=
  (AbsoluteValue.isNonarchimedean_iff_bounded_nat
    (HeightOneSpectrum.adicAbv K v)).1
      (HeightOneSpectrum.isNonarchimedean_adicAbv K v)

open scoped Classical in
/-- Finite-field power-residue symbols commute with a field equivalence.
The statement is made on underlying units so it can be reused with every
roots-of-unity transport occurring below. -/
theorem finiteFieldPowerResidueSymbol_unitsMap_ringEquiv
    {k l : Type*} [Field k] [Field l] [Fintype k] [Fintype l]
    (e : k ≃+* l) (n : ℕ+)
    (hnk : (n : ℕ) ∣ Fintype.card k - 1)
    (hnl : (n : ℕ) ∣ Fintype.card l - 1)
    (u : kˣ) :
    Units.map e.toMonoidHom
        ((AlgebraicNumberTheory.PowerResidueSymbols.finiteFieldPowerResidueSymbol
            k n hnk u :
            rootsOfUnity (n : ℕ) k) : kˣ) =
      ((AlgebraicNumberTheory.PowerResidueSymbols.finiteFieldPowerResidueSymbol
          l n hnl
          (Units.map e.toMonoidHom u) :
            rootsOfUnity (n : ℕ) l) : lˣ) := by
  rw [
    AlgebraicNumberTheory.PowerResidueSymbols.finiteFieldPowerResidueSymbol_apply,
    AlgebraicNumberTheory.PowerResidueSymbols.finiteFieldPowerResidueSymbol_apply,
    map_pow]
  rw [Fintype.card_congr e.toEquiv]

open scoped Classical in
/-- The residue field of a finite-place completion is canonically the
prime-ideal residue field.  The construction passes through the localization
at the prime and then through the residue equivalence induced by completion. -/
noncomputable def finitePlacePrimeResidueEquivLocalResidue
    (v : HeightOneSpectrum (𝓞 K)) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    (𝓞 K ⧸ v.asIdeal) ≃+* 𝓀[C] := by
  let a := HeightOneSpectrum.adicAbv K v
  let ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a :=
    finitePlaceAdicAbv_nonarchimedeanAbsoluteValue K v
  let C := a.Completion
  letI : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let V := LubinTate.Valuations.exponentialValuationSubring
    (AlgebraicNumberTheory.Valuations.absoluteValueExponentialValuation a ha)
  let aC := AbsoluteValue.completionAbsoluteValue a
  let haC : LubinTate.Valuations.NonarchimedeanAbsoluteValue aC :=
    (AbsoluteValue.isNonarchimedean_iff_bounded_nat aC).1
      (AbsoluteValue.completionAbsoluteValue_isNonarchimedean a
        ((AbsoluteValue.isNonarchimedean_iff_bounded_nat a).2 ha))
  let VC := LubinTate.Valuations.exponentialValuationSubring
    (AlgebraicNumberTheory.Valuations.absoluteValueExponentialValuation aC haC)
  let Rv := v.valuationSubringAtPrime K
  letI : IsLocalRing Rv :=
    IsLocalization.AtPrime.isLocalRing Rv v.asIdeal
  have hBase : Rv.toSubring = V := by
    ext x
    rw [AlgebraicNumberTheory.Valuations.mem_absoluteValueExponentialSubring_iff]
    change x ∈ v.valuationSubringAtPrime K ↔ _
    rw [v.valuationSubringAtPrime_eq_valuationSubring]
    change v.valuation K x ≤ 1 ↔ a x ≤ 1
    rw [HeightOneSpectrum.adicAbv_def]
    exact_mod_cast
      (WithZeroMulInt.toNNReal_le_one_iff
        (HeightOneSpectrum.one_lt_absNorm_nnreal v)).symm
  let eBase : Rv ≃+* V := RingEquiv.subringCongr hBase
  have hCompletion : VC = 𝒪[C] := by
    ext x
    rw [AlgebraicNumberTheory.Valuations.mem_absoluteValueExponentialSubring_iff]
    change ‖x‖ ≤ 1 ↔ x ∈ 𝒪[C]
    exact
      (finitePlaceCompletion_mem_integers_iff_norm_le_one
        a (HeightOneSpectrum.isNonarchimedean_adicAbv K v) x).symm
  let eCompletionRing : VC ≃+* 𝒪[C] :=
    RingEquiv.subringCongr hCompletion
  let eIdeal : (𝓞 K ⧸ v.asIdeal) ≃+* v.asIdeal.ResidueField :=
    RingEquiv.ofBijective
      (algebraMap (𝓞 K ⧸ v.asIdeal) v.asIdeal.ResidueField)
      v.asIdeal.bijective_algebraMap_quotient_residueField
  let eLocalization : Localization.AtPrime v.asIdeal ≃ₐ[𝓞 K] Rv :=
    IsLocalization.algEquiv v.asIdeal.primeCompl _ _
  exact
    eIdeal |>.trans
      (IsLocalRing.ResidueField.mapEquiv eLocalization.toRingEquiv) |>.trans
      (IsLocalRing.ResidueField.mapEquiv eBase) |>.trans
      (AlgebraicNumberTheory.Valuations.completionResidueEquiv a ha) |>.trans
      (IsLocalRing.ResidueField.mapEquiv eCompletionRing)

open scoped Classical in
/-- The image of an algebraic integer in the valuation ring of a finite-place
completion. -/
noncomputable def finitePlaceIntegralCompletionElement
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    𝒪[C] := by
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  letI : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  exact ⟨algebraMap K C (x : K), by
    rw [finitePlaceCompletion_mem_integers_iff_norm_le_one
      (HeightOneSpectrum.adicAbv K v)
      (HeightOneSpectrum.isNonarchimedean_adicAbv K v)]
    calc
      ‖algebraMap K C (x : K)‖ =
          HeightOneSpectrum.adicAbv K v (x : K) :=
        AbsoluteValue.completionAbsoluteValue_coe
          (HeightOneSpectrum.adicAbv K v) (x : K)
      _ ≤ 1 :=
        v.adicAbv_coe_le_one
          (HeightOneSpectrum.one_lt_absNorm_nnreal v) x⟩

open scoped Classical in
/-- The finite-place integral element has the expected underlying completion
value. -/
theorem finitePlaceIntegralCompletionElement_coe
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    (finitePlaceIntegralCompletionElement K v x : C) =
      algebraMap K C (x : K) :=
  rfl

open scoped Classical in
/-- The finite-place residue equivalence sends the class of an algebraic
integer to the residue of its canonical image in the completion. -/
@[simp]
theorem finitePlacePrimeResidueEquivLocalResidue_mk
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    finitePlacePrimeResidueEquivLocalResidue K v
        (Ideal.Quotient.mk v.asIdeal x) =
      IsLocalRing.residue 𝒪[C]
        (finitePlaceIntegralCompletionElement K v x) := by
  simp only [finitePlacePrimeResidueEquivLocalResidue,
    finitePlaceIntegralCompletionElement, RingEquiv.trans_apply]
  rw [RingEquiv.ofBijective_apply,
    Ideal.algebraMap_quotient_residueField_mk]
  rw [IsScalarTower.algebraMap_apply
    (NumberField.RingOfIntegers K) (Localization.AtPrime v.asIdeal)]
  rw [IsLocalRing.ResidueField.algebraMap_eq]
  simp only [IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue]
  rw [AlgebraicNumberTheory.Valuations.completionResidueEquiv_residue]
  simp only [IsLocalRing.ResidueField.map_residue]
  congr 1
  apply Subtype.ext
  change
    algebraMap K (HeightOneSpectrum.adicAbv K v).Completion
        (((IsLocalization.algEquiv v.asIdeal.primeCompl
            (Localization.AtPrime v.asIdeal)
            (v.valuationSubringAtPrime K))
          (algebraMap (𝓞 K) (Localization.AtPrime v.asIdeal) x) :
        v.valuationSubringAtPrime K) : K) =
      algebraMap K (HeightOneSpectrum.adicAbv K v).Completion (x : K)
  rw [AlgEquiv.commutes]
  rw [IsScalarTower.algebraMap_apply
    (NumberField.RingOfIntegers K) (v.valuationSubringAtPrime K)]
  rfl

open scoped Classical in
/-- A nonzero algebraic integer, regarded as a global field unit. -/
def nonzeroIntegralFieldUnit (x : 𝓞 K) (hx : x ≠ 0) : Kˣ :=
  Units.mk0 (x : K) (by
    intro hxK
    apply hx
    apply Subtype.ext
    exact hxK)

omit [NumberField K] in
open scoped Classical in
@[simp]
theorem nonzeroIntegralFieldUnit_coe (x : 𝓞 K) (hx : x ≠ 0) :
    ((nonzeroIntegralFieldUnit K x hx : Kˣ) : K) = (x : K) :=
  rfl

open scoped Classical in
/-- An algebraic integer avoiding a prime ideal, regarded as a nonzero
element of the global field. -/
noncomputable def primeAvoidingIntegralFieldUnit
    (v : HeightOneSpectrum (𝓞 K))
    (x : 𝓞 K) (hx : x ∉ v.asIdeal) : Kˣ :=
  nonzeroIntegralFieldUnit K x (by
    intro hx0
    apply hx
    rw [hx0]
    exact Ideal.zero_mem _)

omit [NumberField K] in
open scoped Classical in
@[simp]
theorem primeAvoidingIntegralFieldUnit_coe
    (v : HeightOneSpectrum (𝓞 K))
    (x : 𝓞 K) (hx : x ∉ v.asIdeal) :
    ((primeAvoidingIntegralFieldUnit K v x hx : Kˣ) : K) = (x : K) :=
  rfl

open scoped Classical in
/-- An algebraic integer nonzero modulo `v`, regarded as a unit of the
valuation ring of the finite-place completion. -/
noncomputable def finitePlaceIntegralCompletionUnit
    (v : HeightOneSpectrum (𝓞 K))
    (x : 𝓞 K) (hx : x ∉ v.asIdeal) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    𝒪[C]ˣ := by
  let a := HeightOneSpectrum.adicAbv K v
  let C := a.Completion
  letI : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let y : C := algebraMap K C (x : K)
  have hyNorm : ‖y‖ = 1 := by
    calc
      ‖y‖ = a (x : K) :=
        AbsoluteValue.completionAbsoluteValue_coe a (x : K)
      _ = ‖NumberField.FinitePlace.embedding v (x : K)‖ :=
        (NumberField.FinitePlace.norm_embedding v (x : K)).symm
      _ = 1 :=
        (NumberField.FinitePlace.norm_eq_one_iff_notMem K v x).2 hx
  have hyNe : y ≠ 0 := by
    intro hy
    rw [hy, norm_zero] at hyNorm
    exact zero_ne_one hyNorm
  let yIntegral : 𝒪[C] := ⟨y, by
    rw [finitePlaceCompletion_mem_integers_iff_norm_le_one
      a (HeightOneSpectrum.isNonarchimedean_adicAbv K v)]
    exact hyNorm.le⟩
  let yInvIntegral : 𝒪[C] := ⟨y⁻¹, by
    rw [finitePlaceCompletion_mem_integers_iff_norm_le_one
      a (HeightOneSpectrum.isNonarchimedean_adicAbv K v),
      norm_inv, hyNorm, inv_one]⟩
  exact {
    val := yIntegral
    inv := yInvIntegral
    val_inv := by
      apply Subtype.ext
      exact mul_inv_cancel₀ hyNe
    inv_val := by
      apply Subtype.ext
      exact inv_mul_cancel₀ hyNe }

open scoped Classical in
/-- Forgetting the integral-unit structure recovers the ordinary image of
the algebraic integer in the finite-place completion. -/
theorem finitePlaceIntegralCompletionUnit_coe
    (v : HeightOneSpectrum (𝓞 K))
    (x : 𝓞 K) (hx : x ∉ v.asIdeal) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    (((finitePlaceIntegralCompletionUnit K v x hx : 𝒪[C]ˣ) : 𝒪[C]) : C) =
      algebraMap K C (x : K) := by
  rfl

open scoped Classical in
/-- The completion image of a prime-avoiding algebraic integer is the field
unit underlying its canonical valuation-ring unit. -/
theorem finitePlaceHilbert_completionUnit_primeAvoidingIntegralFieldUnit
    (v : HeightOneSpectrum (𝓞 K))
    (x : 𝓞 K) (hx : x ∉ v.asIdeal) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    finitePlaceHilbertCompletionUnit K v
        (primeAvoidingIntegralFieldUnit K v x hx) =
      integerUnitsToFieldUnits C
        (finitePlaceIntegralCompletionUnit K v x hx) := by
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  let : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  dsimp only
  apply Units.ext
  change
    algebraMap K C (x : K) =
      (((finitePlaceIntegralCompletionUnit K v x hx : 𝒪[C]ˣ) :
        𝒪[C]) : C)
  exact (finitePlaceIntegralCompletionUnit_coe K v x hx).symm

open scoped Classical in
/-- As an element of the completion valuation ring, the lifted unit is the
canonical lifted algebraic integer. -/
@[simp]
theorem finitePlaceIntegralCompletionUnit_val
    (v : HeightOneSpectrum (𝓞 K))
    (x : 𝓞 K) (hx : x ∉ v.asIdeal) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    (finitePlaceIntegralCompletionUnit K v x hx : 𝒪[C]) =
      finitePlaceIntegralCompletionElement K v x := by
  dsimp only
  apply Subtype.ext
  exact finitePlaceIntegralCompletionUnit_coe K v x hx

open scoped Classical in
/-- Reduction of the canonical completion unit agrees with reduction modulo
the corresponding global prime ideal. -/
theorem finitePlace_integerUnitsToResidueUnits_integralUnit
    (v : HeightOneSpectrum (𝓞 K))
    (x : 𝓞 K) (hx : x ∉ v.asIdeal) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    integerUnitsToResidueUnits C
        (finitePlaceIntegralCompletionUnit K v x hx) =
      Units.map
        (finitePlacePrimeResidueEquivLocalResidue K v).toMonoidHom
        (AlgebraicNumberTheory.PowerResidueSymbols.primeIdealResidueUnit
          K v x hx) := by
  dsimp only
  apply Units.ext
  change
    IsLocalRing.residue 𝒪[(HeightOneSpectrum.adicAbv K v).Completion]
        (finitePlaceIntegralCompletionUnit K v x hx :
          𝒪[(HeightOneSpectrum.adicAbv K v).Completion]) =
      finitePlacePrimeResidueEquivLocalResidue K v
        (Ideal.Quotient.mk v.asIdeal x)
  simpa only [finitePlaceIntegralCompletionUnit_val] using
    (finitePlacePrimeResidueEquivLocalResidue_mk K v x).symm

open scoped Classical in
/-- The canonical inclusion from integral roots of unity into the common
field-valued group used by the global Hilbert symbols. -/
def integralRootsOfUnityToNthRoots
    (n : ℕ) :
    rootsOfUnity n (𝓞 K) →* nthRootsSubgroup K n where
  toFun z :=
    ⟨Units.map (algebraMap (𝓞 K) K).toMonoidHom z.1, by
      calc
        Units.map (algebraMap (𝓞 K) K).toMonoidHom z.1 ^ n =
            Units.map (algebraMap (𝓞 K) K).toMonoidHom (z.1 ^ n) :=
          (map_pow
            (Units.map (algebraMap (𝓞 K) K).toMonoidHom) z.1 n).symm
        _ = 1 := by rw [z.2, map_one]⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (Units.map (algebraMap (𝓞 K) K).toMonoidHom)
  map_mul' := by
    intro z w
    apply Subtype.ext
    exact map_mul
      (Units.map (algebraMap (𝓞 K) K).toMonoidHom) z.1 w.1

omit [NumberField K] in
open scoped Classical in
/-- The integral-root inclusion is the underlying unit map. -/
@[simp]
theorem integralRootsOfUnityToNthRoots_apply
    (n : ℕ) (z : rootsOfUnity n (𝓞 K)) :
    (integralRootsOfUnityToNthRoots K n z).1 =
      Units.map (algebraMap (𝓞 K) K).toMonoidHom z.1 :=
  rfl

omit [NumberField K] in
open scoped Classical in
/-- The integral-to-field inclusion is injective on roots of unity. -/
theorem integralRootsOfUnityToNthRoots_injective
    (n : ℕ) :
    Function.Injective (integralRootsOfUnityToNthRoots K n) := by
  intro z w h
  apply Subtype.ext
  apply
    (Units.map_injective
      (f := (algebraMap (𝓞 K) K).toMonoidHom)
      RingOfIntegers.coe_injective)
  exact congrArg Subtype.val h

open scoped Classical in
/-- Reduction after embedding an integral global root of unity into a
finite-place completion is the transport of reduction modulo the
corresponding prime ideal. -/
theorem finitePlace_localNthRootsReduction_integralRoots
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (z : rootsOfUnity (n : ℕ) (𝓞 K)) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    (localNthRootsReduction C n
        (nthRootsSubgroupMap K C (n : ℕ)
          (integralRootsOfUnityToNthRoots K (n : ℕ) z))).1 =
      Units.map
        (finitePlacePrimeResidueEquivLocalResidue K v).toMonoidHom
        (AlgebraicNumberTheory.PowerResidueSymbols.rootsOfUnityReduction
          K v (n : ℕ) z).1 := by
  dsimp only
  apply Units.ext
  change
    IsLocalRing.residue 𝒪[(HeightOneSpectrum.adicAbv K v).Completion]
        (nthRootIntegerUnit
          (HeightOneSpectrum.adicAbv K v).Completion n
          (nthRootsSubgroupMap K
            (HeightOneSpectrum.adicAbv K v).Completion (n : ℕ)
            (integralRootsOfUnityToNthRoots K (n : ℕ) z)) :
          𝒪[(HeightOneSpectrum.adicAbv K v).Completion]) =
      finitePlacePrimeResidueEquivLocalResidue K v
        (Ideal.Quotient.mk v.asIdeal (z.1 : 𝓞 K))
  rw [finitePlacePrimeResidueEquivLocalResidue_mk]
  congr 1

open scoped Classical in
/-- The integral principal ideal generated by the exponent. -/
def powerResidueExponentIdeal (n : ℕ+) : Ideal (𝓞 K) :=
  Ideal.span {((n : ℕ) : 𝓞 K)}

open scoped Classical in
/-- The exponent ideal is nonzero in a number field. -/
theorem powerResidueExponentIdeal_ne_zero (n : ℕ+) :
    powerResidueExponentIdeal K n ≠ 0 := by
  change Ideal.span {((n : ℕ) : 𝓞 K)} ≠ ⊥
  exact Ideal.span_singleton_eq_bot.not.mpr
    (Nat.cast_ne_zero.mpr n.ne_zero)

omit [NumberField K] in
open scoped Classical in
private theorem ideal_span_singleton_ne_zero
    {x : 𝓞 K} (hx : x ≠ 0) : Ideal.span {x} ≠ 0 :=
  Submodule.span_singleton_eq_bot.mp.mt hx

open scoped Classical in
/-- The finite places dividing the exponent.  These, together with all
infinite places, are precisely the correction places in the reciprocity
formula once the two principal denominator supports are removed. -/
noncomputable def powerResidueExponentFinitePlaces
    (n : ℕ+) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (Ideal.finite_factors
    (powerResidueExponentIdeal_ne_zero K n)).toFinset

open scoped Classical in
/-- Membership in the exponent-place support is divisibility by the exponent
ideal. -/
@[simp]
theorem mem_powerResidueExponentFinitePlaces_iff
    (n : ℕ+) (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ powerResidueExponentFinitePlaces K n ↔
      v.asIdeal ∣ powerResidueExponentIdeal K n :=
  Set.Finite.mem_toFinset
    (Ideal.finite_factors
      (powerResidueExponentIdeal_ne_zero K n))

open scoped Classical in
/-- At a finite place not dividing the exponent, the exponent is a unit in
the canonical completion. -/
theorem finitePlace_natCast_valuation_eq_one_of_not_mem_exponent
    (n : ℕ+) (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ powerResidueExponentFinitePlaces K n) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    ValuativeRel.valuation C ((n : ℕ) : C) = 1 := by
  dsimp only
  let : IsUltrametricDist
      (HeightOneSpectrum.adicAbv K v).Completion :=
    finitePlaceArtinCompletionIsUltrametricDist
      (HeightOneSpectrum.adicAbv K v)
      (HeightOneSpectrum.isNonarchimedean_adicAbv K v)
  have hvNotDvd :
      ¬ v.asIdeal ∣ powerResidueExponentIdeal K n := by
    simpa only [mem_powerResidueExponentFinitePlaces_iff] using hv
  have hvNotMem : ((n : ℕ) : 𝓞 K) ∉ v.asIdeal := by
    intro hvMem
    apply hvNotDvd
    rw [powerResidueExponentIdeal, Ideal.dvd_span_singleton]
    exact hvMem
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  have hNorm : ‖((n : ℕ) : C)‖ = 1 := by
    calc
      ‖((n : ℕ) : C)‖ =
          ‖algebraMap K C (((n : ℕ) : K))‖ := by rw [map_natCast]
      _ = HeightOneSpectrum.adicAbv K v (((n : ℕ) : K)) :=
        AbsoluteValue.completionAbsoluteValue_coe
          (HeightOneSpectrum.adicAbv K v) (((n : ℕ) : K))
      _ = ‖NumberField.FinitePlace.embedding v (((n : ℕ) : K))‖ :=
        (NumberField.FinitePlace.norm_embedding v (((n : ℕ) : K))).symm
      _ = 1 :=
        (NumberField.FinitePlace.norm_eq_one_iff_notMem K v
          (((n : ℕ) : 𝓞 K))).2 hvNotMem
  let vCNorm := NormedField.valuation (K := C)
  let : vCNorm.Compatible := Valuation.Compatible.ofValuation vCNorm
  have hnCNorm : vCNorm ((n : ℕ) : C) = 1 := by
    change ‖((n : ℕ) : C)‖₊ = 1
    exact NNReal.eq (by simpa using hNorm)
  exact
    (ValuativeRel.isEquiv vCNorm (ValuativeRel.valuation C))
      |>.eq_one_iff_eq_one.mp hnCNorm

open scoped Classical in
private noncomputable def finitePlaceLocalTamePowerResidueSymbolValue
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hv : v ∉ powerResidueExponentFinitePlaces K n)
    (a : 𝓞 K) (ha : a ∉ v.asIdeal) :
    nthRootsSubgroup (HeightOneSpectrum.adicAbv K v).Completion (n : ℕ) := by
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  letI : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  exact localTamePowerResidueSymbol C n
    (finitePlace_natCast_valuation_eq_one_of_not_mem_exponent K n v hv)
    (finitePlaceHilbert_primitiveRoots_nonempty K n hmu v)
    (finitePlaceIntegralCompletionUnit K v a ha)

open scoped Classical in
private noncomputable def finitePlaceLocalTamePowerResidueSymbolFieldValue
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hv : v ∉ powerResidueExponentFinitePlaces K n)
    (a : 𝓞 K) (ha : a ∉ v.asIdeal) :
    (HeightOneSpectrum.adicAbv K v).Completion :=
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  letI : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  ((localTamePowerResidueSymbol C n
      (finitePlace_natCast_valuation_eq_one_of_not_mem_exponent K n v hv)
      (finitePlaceHilbert_primitiveRoots_nonempty K n hmu v)
      (finitePlaceIntegralCompletionUnit K v a ha)).1 : C)

open scoped Classical in
private noncomputable def finitePlacePrimeIdealPowerResidueIntegralRoot
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm v.asIdeal).Coprime (n : ℕ))
    (a : 𝓞 K) (ha : a ∉ v.asIdeal) :
    rootsOfUnity (n : ℕ) (𝓞 K) :=
  AlgebraicNumberTheory.PowerResidueSymbols.primeIdealPowerResidueSymbol
    K v n hmu hcoprime a ha

open scoped Classical in
private noncomputable def finitePlacePrimeIdealPowerResidueGlobalRoot
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm v.asIdeal).Coprime (n : ℕ))
    (a : 𝓞 K) (ha : a ∉ v.asIdeal) : nthRootsSubgroup K (n : ℕ) :=
  integralRootsOfUnityToNthRoots K (n : ℕ)
    (finitePlacePrimeIdealPowerResidueIntegralRoot K v n hmu hcoprime a ha)

open scoped Classical in
private noncomputable def finitePlacePrimeIdealPowerResidueFactorValue
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm v.asIdeal).Coprime (n : ℕ))
    (a : 𝓞 K) (ha : a ∉ v.asIdeal) :
    nthRootsSubgroup (HeightOneSpectrum.adicAbv K v).Completion (n : ℕ) :=
  nthRootsSubgroupMap K (HeightOneSpectrum.adicAbv K v).Completion (n : ℕ)
    (finitePlacePrimeIdealPowerResidueGlobalRoot K v n hmu hcoprime a ha)

open scoped Classical in
private noncomputable def finitePlacePrimeIdealPowerResidueFactorFieldValue
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm v.asIdeal).Coprime (n : ℕ))
    (a : 𝓞 K) (ha : a ∉ v.asIdeal) :
    (HeightOneSpectrum.adicAbv K v).Completion :=
  (((nthRootsSubgroupMap K
      (HeightOneSpectrum.adicAbv K v).Completion (n : ℕ))
    (finitePlacePrimeIdealPowerResidueGlobalRoot K v n hmu hcoprime a ha)).1 :
      (HeightOneSpectrum.adicAbv K v).Completion)

open scoped Classical in
private noncomputable def finitePlaceLocalTamePowerResidueSymbolResidueValue
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hv : v ∉ powerResidueExponentFinitePlaces K n)
    (a : 𝓞 K) (ha : a ∉ v.asIdeal) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    𝓀[C] := by
  dsimp only
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  letI : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  letI : Fintype 𝓀[C] := Fintype.ofFinite _
  have hnLocal : (n : ℕ) ∣ Fintype.card 𝓀[C] - 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact dvd_residueCard_sub_one_of_primitiveRoots C n
      (finitePlace_natCast_valuation_eq_one_of_not_mem_exponent K n v hv)
      (finitePlaceHilbert_primitiveRoots_nonempty K n hmu v)
  exact
    (((AlgebraicNumberTheory.PowerResidueSymbols.finiteFieldPowerResidueSymbol
        𝓀[C] n hnLocal
        (integerUnitsToResidueUnits C
          (finitePlaceIntegralCompletionUnit K v a ha)) :
      rootsOfUnity (n : ℕ) 𝓀[C]).1 : 𝓀[C]ˣ) : 𝓀[C])

open scoped Classical in
private noncomputable def finitePlacePrimeIdealPowerResidueFactorResidueValue
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm v.asIdeal).Coprime (n : ℕ))
    (a : 𝓞 K) (ha : a ∉ v.asIdeal) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    𝓀[C] := by
  dsimp only
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  letI : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  exact
    (((localNthRootsReduction C n
        (nthRootsSubgroupMap K C (n : ℕ)
          (integralRootsOfUnityToNthRoots K (n : ℕ)
            (AlgebraicNumberTheory.PowerResidueSymbols.primeIdealPowerResidueSymbol
              K v n hmu hcoprime a ha)))).1 : 𝓀[C]ˣ) : 𝓀[C])

open scoped Classical in
open AlgebraicNumberTheory.PowerResidueSymbols renaming
  rootsOfUnityReductionEquiv_primeIdealPowerResidueSymbol →
    rootsOfUnityReductionEquiv_primeIdealPowerResidueSymbol in
/-- The tame symbol in a finite-place completion is the image of the
prime-ideal power-residue symbol.  All comparisons are canonical: the only
place hypothesis says that the place does not divide the exponent. -/
private theorem finitePlaceLocalTamePowerResidueSymbol_residueValue_eq
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm v.asIdeal).Coprime (n : ℕ))
    (hv : v ∉ powerResidueExponentFinitePlaces K n)
    (a : 𝓞 K) (ha : a ∉ v.asIdeal) :
    finitePlaceLocalTamePowerResidueSymbolResidueValue K v n hmu hv a ha =
      finitePlacePrimeIdealPowerResidueFactorResidueValue
        K v n hmu hcoprime a ha := by
  unfold finitePlaceLocalTamePowerResidueSymbolResidueValue
  unfold finitePlacePrimeIdealPowerResidueFactorResidueValue
  dsimp only
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  let : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  let : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  let : Fintype 𝓀[C] := Fintype.ofFinite _
  let hnC := finitePlace_natCast_valuation_eq_one_of_not_mem_exponent K n v hv
  let hmuC := finitePlaceHilbert_primitiveRoots_nonempty K n hmu v
  have hnPrime :
      (n : ℕ) ∣ Fintype.card (𝓞 K ⧸ v.asIdeal) - 1 := by
    rw [AlgebraicNumberTheory.PowerResidueSymbols.card_primeIdealResidueField K v]
    exact
      AlgebraicNumberTheory.PowerResidueSymbols.dvd_absNorm_sub_one_of_primitiveRoots
        K v n hmu hcoprime
  have hnLocal : (n : ℕ) ∣ Fintype.card 𝓀[C] - 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact dvd_residueCard_sub_one_of_primitiveRoots C n hnC hmuC
  rw [finitePlace_localNthRootsReduction_integralRoots]
  rw [← AlgebraicNumberTheory.PowerResidueSymbols.rootsOfUnityReductionEquiv_apply
      K v n hmu hcoprime,
    rootsOfUnityReductionEquiv_primeIdealPowerResidueSymbol
      K v n hmu hcoprime a ha]
  rw [finitePlace_integerUnitsToResidueUnits_integralUnit]
  exact congrArg (fun u : 𝓀[C]ˣ => (u : 𝓀[C]))
    (finiteFieldPowerResidueSymbol_unitsMap_ringEquiv
      (finitePlacePrimeResidueEquivLocalResidue K v)
      n hnPrime hnLocal
      (AlgebraicNumberTheory.PowerResidueSymbols.primeIdealResidueUnit
        K v a ha)).symm

open scoped Classical in
private theorem finitePlaceLocalTamePowerResidueSymbolFieldValue_eq_primeIdealValue
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm v.asIdeal).Coprime (n : ℕ))
    (hv : v ∉ powerResidueExponentFinitePlaces K n)
    (a : 𝓞 K) (ha : a ∉ v.asIdeal) :
    @Eq (HeightOneSpectrum.adicAbv K v).Completion
      (finitePlaceLocalTamePowerResidueSymbolFieldValue K v n hmu hv a ha)
      (finitePlacePrimeIdealPowerResidueFactorFieldValue
        K v n hmu hcoprime a ha) := by
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  let : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let hnC :=
    finitePlace_natCast_valuation_eq_one_of_not_mem_exponent K n v hv
  let hmuC := finitePlaceHilbert_primitiveRoots_nonempty K n hmu v
  unfold finitePlaceLocalTamePowerResidueSymbolFieldValue
  unfold finitePlacePrimeIdealPowerResidueFactorFieldValue
  unfold finitePlacePrimeIdealPowerResidueGlobalRoot
  unfold finitePlacePrimeIdealPowerResidueIntegralRoot
  have hRoots :
      localTamePowerResidueSymbol C n hnC hmuC
          (finitePlaceIntegralCompletionUnit K v a ha) =
        nthRootsSubgroupMap K C (n : ℕ)
          (integralRootsOfUnityToNthRoots K (n : ℕ)
            (AlgebraicNumberTheory.PowerResidueSymbols.primeIdealPowerResidueSymbol
              K v n hmu hcoprime a ha)) := by
    apply (localNthRootsReductionEquiv C n hnC hmuC).injective
    rw [localNthRootsReductionEquiv_localTamePowerResidueSymbol]
    apply Subtype.ext
    apply Units.ext
    have hResidue := finitePlaceLocalTamePowerResidueSymbol_residueValue_eq
      K v n hmu hcoprime hv a ha
    unfold finitePlaceLocalTamePowerResidueSymbolResidueValue at hResidue
    unfold finitePlacePrimeIdealPowerResidueFactorResidueValue at hResidue
    dsimp only at hResidue
    exact hResidue
  exact congrArg (fun q : nthRootsSubgroup C (n : ℕ) => (q.1 : C)) hRoots

open scoped Classical in
/-- The normalized additive valuation of a global field unit in the
canonical completion at a finite place. -/
noncomputable def finitePlaceNormalizedValuation
    (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) : ℤ := by
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  letI : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  exact valuationMap C
    (Additive.ofMul (finitePlaceHilbertCompletionUnit K v x))

open scoped Classical in
/-- Away from the exponent, a finite-place Hilbert factor with integral-unit
first entry is the prime-ideal power-residue symbol raised to the negative
normalized valuation of the second entry. -/
theorem finitePlaceHilbertSymbol_eq_primeIdealPowerResidueFactor_zpow
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ powerResidueExponentFinitePlaces K n)
    (hcoprime : (Ideal.absNorm v.asIdeal).Coprime (n : ℕ))
    (a : 𝓞 K) (ha : a ∉ v.asIdeal) (b : Kˣ) :
    finitePlaceHilbertSymbol K n hnK hmu v
        (primeAvoidingIntegralFieldUnit K v a ha) b =
      integralRootsOfUnityToNthRoots K (n : ℕ)
          (AlgebraicNumberTheory.PowerResidueSymbols.primeIdealPowerResidueSymbol
              K v n hmu hcoprime a ha) ^
        (-finitePlaceNormalizedValuation K v b) := by
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  let : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let hnC :=
    finitePlace_natCast_valuation_eq_one_of_not_mem_exponent K n v hv
  let hmuC := finitePlaceHilbert_primitiveRoots_nonempty K n hmu v
  let bC := finitePlaceHilbertCompletionUnit K v b
  apply nthRootsSubgroupMap_injective K C (n : ℕ)
  rw [finitePlaceHilbertSymbol_map_eq_localHilbertSymbol]
  change
    localHilbertSymbol C n
        (finitePlaceHilbert_natCast_ne_zero K n hnK v) hmuC
        (finitePlaceHilbertCompletionUnit K v
          (primeAvoidingIntegralFieldUnit K v a ha)) bC =
      nthRootsSubgroupMap K C (n : ℕ)
        (integralRootsOfUnityToNthRoots K (n : ℕ)
            (AlgebraicNumberTheory.PowerResidueSymbols.primeIdealPowerResidueSymbol
                K v n hmu hcoprime a ha) ^
          (-finitePlaceNormalizedValuation K v b))
  rw [finitePlaceHilbert_completionUnit_primeAvoidingIntegralFieldUnit]
  rw [localHilbertSymbol_tame_formula C n hnC hmuC]
  change
    finitePlaceLocalTamePowerResidueSymbolValue K v n hmu hv a ha ^
        (-finitePlaceNormalizedValuation K v b) = _
  have hBase :
      finitePlaceLocalTamePowerResidueSymbolValue K v n hmu hv a ha =
        finitePlacePrimeIdealPowerResidueFactorValue
          K v n hmu hcoprime a ha := by
    apply Subtype.ext
    apply Units.ext
    simpa only [finitePlaceLocalTamePowerResidueSymbolValue,
      finitePlacePrimeIdealPowerResidueFactorValue,
      finitePlaceLocalTamePowerResidueSymbolFieldValue,
      finitePlacePrimeIdealPowerResidueFactorFieldValue] using
      finitePlaceLocalTamePowerResidueSymbolFieldValue_eq_primeIdealValue
        K v n hmu hcoprime hv a ha
  rw [hBase]
  unfold finitePlacePrimeIdealPowerResidueFactorValue
  unfold finitePlacePrimeIdealPowerResidueGlobalRoot
  unfold finitePlacePrimeIdealPowerResidueIntegralRoot
  rw [map_zpow]

open scoped Classical in
/-- Endpoint form of the finite-place local/global power-residue comparison. -/
theorem finitePlaceHilbertSymbol_eq_primeIdealPowerResidueFactor
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ powerResidueExponentFinitePlaces K n)
    (hcoprime : (Ideal.absNorm v.asIdeal).Coprime (n : ℕ))
    (a : 𝓞 K) (ha : a ∉ v.asIdeal) (b : Kˣ) :
    finitePlaceHilbertSymbol K n hnK hmu v
        (primeAvoidingIntegralFieldUnit K v a ha) b =
      integralRootsOfUnityToNthRoots K (n : ℕ)
          (AlgebraicNumberTheory.PowerResidueSymbols.primeIdealPowerResidueSymbol
              K v n hmu hcoprime a ha) ^
        (-finitePlaceNormalizedValuation K v b) :=
  finitePlaceHilbertSymbol_eq_primeIdealPowerResidueFactor_zpow
    K n hnK hmu v hv hcoprime a ha b

open scoped Classical in
/-- The Dedekind prime multiplicity is the exponent occurring in the
integer-valued adic valuation. -/
theorem intValuation_eq_exp_neg_idealPrimeMultiplicity
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0) :
    v.intValuation x =
      WithZero.exp
        (-(AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeMultiplicity K v (Ideal.span {x})
          : ℤ)) := by
  rw [v.intValuation_if_neg hx]
  rfl

open scoped Classical in
/-- For an integral element, the normalized valuation in the canonical
finite-place completion is the negative multiplicity of the prime in its
principal ideal. -/
theorem finitePlaceNormalizedValuation_nonzeroIntegralFieldUnit
    (v : HeightOneSpectrum (𝓞 K))
    (x : 𝓞 K) (hx : x ≠ 0) :
    finitePlaceNormalizedValuation K v
        (nonzeroIntegralFieldUnit K x hx) =
      -(AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeMultiplicity K v (Ideal.span {x}) :
        ℤ) := by
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  let : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let : IsUltrametricDist C :=
    finitePlaceArtinCompletionIsUltrametricDist
      (HeightOneSpectrum.adicAbv K v)
      (HeightOneSpectrum.isNonarchimedean_adicAbv K v)
  let m := AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeMultiplicity K v (Ideal.span {x})
  let πData := chosenFinitePlaceCompletionIntegralUniformizer v
  have hπIrreducible : Irreducible πData.completionInteger := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    let completionDVF :
        ValuationTheory.DiscreteValuationField.DVF C :=
      { ValueGroup := ValuativeRel.ValueGroupWithZero C
        valuation := ValuativeRel.valuation C }
    exact
      completionDVF.maximalIdeal_eq_span_uniformizer
        πData.completionInteger_isUniformizer
  let πC : Cˣ :=
    Units.mk0 (πData.completionInteger : C)
      πData.completionInteger_isUniformizer.ne_zero
  let xC : Cˣ :=
    finitePlaceHilbertCompletionUnit K v
      (nonzeroIntegralFieldUnit K x hx)
  have hIntX :
      v.intValuation x = WithZero.exp (-(m : ℤ)) := by
    exact intValuation_eq_exp_neg_idealPrimeMultiplicity K v x hx
  have hIntPiPow :
      v.intValuation (πData.integer ^ m) =
        WithZero.exp (-(m : ℤ)) := by
    rw [map_pow, πData.intValuation_eq_exp_neg_one]
    calc
      WithZero.exp (-1 : ℤ) ^ m =
          WithZero.exp (m • (-1 : ℤ)) :=
        (WithZero.exp_nsmul m (-1 : ℤ)).symm
      _ = WithZero.exp (-(m : ℤ)) := by simp
  have hnormX :
      ‖(xC : C)‖ =
        (WithZeroMulInt.toNNReal
          (HeightOneSpectrum.absNorm_ne_zero v)
          (WithZero.exp (-(m : ℤ))) : ℝ) := by
    change ‖algebraMap K C (x : K)‖ = _
    calc
      ‖algebraMap K C (x : K)‖ =
          HeightOneSpectrum.adicAbv K v (x : K) :=
        AbsoluteValue.completionAbsoluteValue_coe
          (HeightOneSpectrum.adicAbv K v) (x : K)
      _ = _ := by
        rw [HeightOneSpectrum.adicAbv_def,
          HeightOneSpectrum.valuation_of_algebraMap, hIntX]
  have hnormPiPow :
      ‖((πC ^ m : Cˣ) : C)‖ =
        (WithZeroMulInt.toNNReal
          (HeightOneSpectrum.absNorm_ne_zero v)
          (WithZero.exp (-(m : ℤ))) : ℝ) := by
    have hπC :
        (πC : C) = algebraMap K C (πData.integer : K) := by
      exact πData.coe_completionInteger
    have hπCPow :
        ((πC ^ m : Cˣ) : C) =
          algebraMap K C (((πData.integer ^ m : 𝓞 K) : K)) := by
      have hIntegerPow :
          (((πData.integer ^ m : 𝓞 K) : K)) =
            (πData.integer : K) ^ m := by
        exact map_pow (algebraMap (𝓞 K) K) πData.integer m
      rw [Units.val_pow_eq_pow_val, hπC, hIntegerPow, map_pow]
    calc
      ‖((πC ^ m : Cˣ) : C)‖ =
          ‖algebraMap K C ((πData.integer ^ m : 𝓞 K) : K)‖ :=
        congrArg norm hπCPow
      _ = HeightOneSpectrum.adicAbv K v
          ((πData.integer ^ m : 𝓞 K) : K) :=
        AbsoluteValue.completionAbsoluteValue_coe
          (HeightOneSpectrum.adicAbv K v)
          ((πData.integer ^ m : 𝓞 K) : K)
      _ =
          (WithZeroMulInt.toNNReal
            (HeightOneSpectrum.absNorm_ne_zero v)
            (WithZero.exp (-(m : ℤ))) : ℝ) := by
        rw [HeightOneSpectrum.adicAbv_def,
          HeightOneSpectrum.valuation_of_algebraMap, hIntPiPow]
  have hraw :
      ValuativeRel.valuation C (xC : C) =
        ValuativeRel.valuation C ((πC ^ m : Cˣ) : C) := by
    apply canonicalValuation_eq_of_valuation_eq
      (v := NormedField.valuation (K := C))
    apply NNReal.eq
    simpa only [NormedField.valuation_apply, coe_nnnorm] using
      hnormX.trans hnormPiPow.symm
  have hValuationMap :
      valuationMap C (Additive.ofMul xC) =
        valuationMap C (Additive.ofMul (πC ^ m)) := by
    rw [valuationMap_apply, valuationMap_apply]
    unfold IsNonarchimedeanLocalField.v
    congr 2
    exact congrArg
      (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt C) hraw
  have hπCValuation :
      valuationMap C (Additive.ofMul πC) = -1 := by
    rw [valuationMap_apply]
    exact
      v_integerRingIrreducibleFieldUnit C πData.completionInteger
        hπIrreducible πC rfl
  calc
    finitePlaceNormalizedValuation K v
        (nonzeroIntegralFieldUnit K x hx) =
        valuationMap C (Additive.ofMul xC) := rfl
    _ = valuationMap C (Additive.ofMul (πC ^ m)) := hValuationMap
    _ = (m : ℤ) * valuationMap C (Additive.ofMul πC) := by
      rw [valuationMap_ofMul_pow]
    _ = -(m : ℤ) := by rw [hπCValuation]; simp
    _ = -(AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeMultiplicity K v (Ideal.span {x})
      : ℤ) := rfl

open scoped Classical in
/-- Prime avoidance is the common special case of the integral valuation
formula used for numerator units. -/
theorem finitePlaceNormalizedValuation_primeAvoidingIntegralFieldUnit
    (v : HeightOneSpectrum (𝓞 K))
    (x : 𝓞 K) (hx : x ∉ v.asIdeal) :
    finitePlaceNormalizedValuation K v
        (primeAvoidingIntegralFieldUnit K v x hx) =
      -(AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeMultiplicity K v (Ideal.span {x}) :
        ℤ) := by
  let hx0 : x ≠ 0 := by
    intro hxzero
    apply hx
    rw [hxzero]
    exact Ideal.zero_mem _
  change finitePlaceNormalizedValuation K v
      (nonzeroIntegralFieldUnit K x hx0) = _
  exact finitePlaceNormalizedValuation_nonzeroIntegralFieldUnit K v x hx0

open scoped Classical in
/-- Integral form of the finite-place comparison: the exponent is the
Dedekind multiplicity in the principal denominator ideal. -/
theorem finitePlaceHilbertSymbol_integral_eq_primeIdealPowerResidueFactor
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ powerResidueExponentFinitePlaces K n)
    (hcoprime : (Ideal.absNorm v.asIdeal).Coprime (n : ℕ))
    (a b : 𝓞 K) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : a ∉ v.asIdeal) :
    finitePlaceHilbertSymbol K n hnK hmu v
        (nonzeroIntegralFieldUnit K a ha0)
        (nonzeroIntegralFieldUnit K b hb0) =
      integralRootsOfUnityToNthRoots K (n : ℕ)
          (AlgebraicNumberTheory.PowerResidueSymbols.primeIdealPowerResidueSymbol
              K v n hmu hcoprime a ha) ^
        AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeMultiplicity K v (Ideal.span {b}) := by
  have haUnits :
      nonzeroIntegralFieldUnit K a ha0 =
        primeAvoidingIntegralFieldUnit K v a ha := by
    apply Units.ext
    rfl
  rw [haUnits,
    finitePlaceHilbertSymbol_eq_primeIdealPowerResidueFactor
      K n hnK hmu v hv hcoprime a ha
        (nonzeroIntegralFieldUnit K b hb0),
    finitePlaceNormalizedValuation_nonzeroIntegralFieldUnit]
  simp only [neg_neg, zpow_natCast]

open scoped Classical in
/-- Finite-place Hilbert symbols inherit skew symmetry from the local
Hilbert symbol in the canonical completion. -/
theorem finitePlaceHilbertSymbol_skew
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ) :
    finitePlaceHilbertSymbol K n hnK hmu v a b =
      (finitePlaceHilbertSymbol K n hnK hmu v b a)⁻¹ := by
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  let : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  apply nthRootsSubgroupMap_injective K C (n : ℕ)
  rw [map_inv,
    finitePlaceHilbertSymbol_map_eq_localHilbertSymbol,
    finitePlaceHilbertSymbol_map_eq_localHilbertSymbol]
  exact
    localHilbertSymbol_skew C n
      (finitePlaceHilbert_natCast_ne_zero K n hnK v)
      (finitePlaceHilbert_primitiveRoots_nonempty K n hmu v)
      (finitePlaceHilbertCompletionUnit K v a)
      (finitePlaceHilbertCompletionUnit K v b)

open scoped Classical in
/-- If two nonzero algebraic integers are both units at a finite place, the
corresponding finite-place Hilbert symbol is trivial. -/
theorem finitePlaceHilbertSymbol_integral_units_eq_one
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ powerResidueExponentFinitePlaces K n)
    (a b : 𝓞 K) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : a ∉ v.asIdeal) (hb : b ∉ v.asIdeal) :
    finitePlaceHilbertSymbol K n hnK hmu v
        (nonzeroIntegralFieldUnit K a ha0)
        (nonzeroIntegralFieldUnit K b hb0) = 1 := by
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  let : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  apply nthRootsSubgroupMap_injective K C (n : ℕ)
  rw [map_one, finitePlaceHilbertSymbol_map_eq_localHilbertSymbol]
  have haUnits :
      finitePlaceHilbertCompletionUnit K v
          (nonzeroIntegralFieldUnit K a ha0) =
        integerUnitsToFieldUnits C
          (finitePlaceIntegralCompletionUnit K v a ha) := by
    apply Units.ext
    change
      algebraMap K C (a : K) =
        (((finitePlaceIntegralCompletionUnit K v a ha : 𝒪[C]ˣ) :
          𝒪[C]) : C)
    exact (finitePlaceIntegralCompletionUnit_coe K v a ha).symm
  have hbUnits :
      finitePlaceHilbertCompletionUnit K v
          (nonzeroIntegralFieldUnit K b hb0) =
        integerUnitsToFieldUnits C
          (finitePlaceIntegralCompletionUnit K v b hb) := by
    apply Units.ext
    change
      algebraMap K C (b : K) =
        (((finitePlaceIntegralCompletionUnit K v b hb : 𝒪[C]ˣ) :
          𝒪[C]) : C)
    exact (finitePlaceIntegralCompletionUnit_coe K v b hb).symm
  unfold finitePlaceLocalHilbertSymbol
  rw [haUnits, hbUnits]
  exact
    localHilbertSymbol_integerUnit_integerUnit_eq_one C n
      (finitePlace_natCast_valuation_eq_one_of_not_mem_exponent K n v hv)
      (finitePlaceHilbert_primitiveRoots_nonempty K n hmu v)
      (finitePlaceIntegralCompletionUnit K v a ha)
      (finitePlaceIntegralCompletionUnit K v b hb)

open scoped Classical in
/-- Primewise comparison between the tame finite-place Hilbert factor and
the quotient of the two ideal power-residue factors. -/
theorem powerResidueAwayFromExponentFiniteFactor_integral_eq_idealFactors
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : 𝓞 K) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hcoprimeA :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ Ideal.span {a} →
          (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (hcoprimeB :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ Ideal.span {b} →
          (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (haB :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ Ideal.span {b} → a ∉ P.asIdeal)
    (hbA :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ Ideal.span {a} → b ∉ P.asIdeal)
    (hAwayA :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ Ideal.span {a} →
          P ∉ powerResidueExponentFinitePlaces K n)
    (hAwayB :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ Ideal.span {b} →
          P ∉ powerResidueExponentFinitePlaces K n)
    (P : HeightOneSpectrum (𝓞 K)) :
    (if P ∈ powerResidueExponentFinitePlaces K n then
        1
      else
        finitePlaceHilbertSymbol K n hnK hmu P
          (nonzeroIntegralFieldUnit K a ha0)
          (nonzeroIntegralFieldUnit K b hb0)) =
      integralRootsOfUnityToNthRoots K (n : ℕ)
          (idealPowerResidueFactor K (Ideal.span {b}) n hmu a
            hcoprimeB haB P) *
        (integralRootsOfUnityToNthRoots K (n : ℕ)
          (idealPowerResidueFactor K (Ideal.span {a}) n hmu b
            hcoprimeA hbA P))⁻¹ := by
  by_cases hPExponent : P ∈ powerResidueExponentFinitePlaces K n
  · have hPA : ¬ P.asIdeal ∣ Ideal.span {a} := by
      intro hPA
      exact (hAwayA P hPA) hPExponent
    have hPB : ¬ P.asIdeal ∣ Ideal.span {b} := by
      intro hPB
      exact (hAwayB P hPB) hPExponent
    simp only [ite_eq_left hPExponent, idealPowerResidueFactor,
      dite_eq_right hPA, dite_eq_right hPB, map_one, inv_one, mul_one]
  · rw [ite_eq_right hPExponent]
    by_cases hPB : P.asIdeal ∣ Ideal.span {b}
    · have haP : a ∉ P.asIdeal := haB P hPB
      have hPA : ¬ P.asIdeal ∣ Ideal.span {a} := by
        intro hPA
        apply haP
        rw [← Ideal.dvd_span_singleton]
        exact hPA
      rw [finitePlaceHilbertSymbol_integral_eq_primeIdealPowerResidueFactor
        K n hnK hmu P (hAwayB P hPB) (hcoprimeB P hPB)
          a b ha0 hb0 haP]
      simp only [idealPowerResidueFactor, dite_eq_left hPB, dite_eq_right hPA,
        map_pow, map_one, inv_one, mul_one]
    · by_cases hPA : P.asIdeal ∣ Ideal.span {a}
      · have hbP : b ∉ P.asIdeal := hbA P hPA
        rw [finitePlaceHilbertSymbol_skew K n hnK hmu]
        rw [finitePlaceHilbertSymbol_integral_eq_primeIdealPowerResidueFactor
          K n hnK hmu P (hAwayA P hPA) (hcoprimeA P hPA)
            b a hb0 ha0 hbP]
        simp only [idealPowerResidueFactor, dite_eq_right hPB, dite_eq_left hPA,
          map_pow, map_one, one_mul]
      · have haP : a ∉ P.asIdeal := by
          intro haMem
          apply hPA
          rw [Ideal.dvd_span_singleton]
          exact haMem
        have hbP : b ∉ P.asIdeal := by
          intro hbMem
          apply hPB
          rw [Ideal.dvd_span_singleton]
          exact hbMem
        rw [finitePlaceHilbertSymbol_integral_units_eq_one
          K n hnK hmu P hPExponent a b ha0 hb0 haP hbP]
        simp only [idealPowerResidueFactor, dite_eq_right hPB, dite_eq_right hPA,
          map_one, inv_one, mul_one]

open scoped Classical in
/-- A concrete finite set containing every finite place where a local
power-residue factor of `a` and `b` may be nontrivial.  Its exponent part is
the exact set of prime divisors of `(n)`. -/
noncomputable def powerResidueBadFinitePlaces
    (n : ℕ+) (a b : Kˣ) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (chosenUnitFiniteSupport (K := K) a ∪
      chosenUnitFiniteSupport (K := K) b) ∪
    powerResidueExponentFinitePlaces K n

open scoped Classical in
/-- The explicit bad-place correction in power-residue reciprocity.  Every
factor already lies in the common group `nthRootsSubgroup K n`. -/
noncomputable def powerResidueBadPlaceCorrection
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : Kˣ) :
    nthRootsSubgroup K (n : ℕ) :=
  (∏ v : InfinitePlace K,
      infinitePlaceHilbertSymbol K n v a b) *
    (∏ v ∈ powerResidueExponentFinitePlaces K n,
      finitePlaceHilbertSymbol K n hnK hmu v a b)

open scoped Classical in
private theorem valuation_eq_one_of_not_mem_chosenUnitFiniteSupport
    (x : Kˣ) (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ chosenUnitFiniteSupport (K := K) x) :
    v.valuation K (x : K) = 1 :=
  (mem_SUnitGroup_iff (K := K)
      (chosenUnitFiniteSupport (K := K) x) x).mp
    (mem_sUnitGroup_chosenUnitFiniteSupport (K := K) x) v hv

open scoped Classical in
/-- The finite-place Hilbert symbol is trivial when the exponent and both
global arguments are units at this place. -/
theorem finitePlaceHilbertSymbol_eq_one_of_valuation_eq_one
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : Kˣ) (v : HeightOneSpectrum (𝓞 K))
    (hva : v.valuation K (a : K) = 1)
    (hvb : v.valuation K (b : K) = 1)
    (hvn : v.valuation K ((n : ℕ) : K) = 1) :
    finitePlaceHilbertSymbol K n hnK hmu v a b = 1 := by
  let L := chosenSimpleKummerExtension K n hnK b
  let : FiniteDimensional K L :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let : IsAbelianGalois K L :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let : NumberField L := NumberField.of_module_finite K L
  have haIntegral :
      IdeleGroup.finiteComponent v (IdeleGroup.principalIdele K a) ∈
        (v.adicCompletionIntegers K).units := by
    rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
    rw [IdeleGroup.finiteComponent_principalIdele,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hva
  have hUnramified :
      Algebra.IsUnramifiedAt (𝓞 K)
        (finitePlaceExtensionCentre
          (K := K) (L := L) v
          (chosenFinitePlaceExtension (L := L) v)).asIdeal := by
    apply
      chosenSimpleKummerExtension_isUnramifiedAt_at_all_finitePlacesAbove_of_valuation_eq_one
        (K := K) n hnK hmu b v hvb hvn
    exact
      finitePlaceBelow_finitePlaceExtensionCentre
        (K := K) (L := L) v
          (chosenFinitePlaceExtension (L := L) v)
  have hArtin :
      chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v
          (IdeleGroup.finiteComponent v (IdeleGroup.principalIdele K a)) = 1 :=
    chosenFinitePlaceArtinMonoidHom_eq_one_of_integral_of_unramifiedAt
      (K := K) (L := L) v (IdeleGroup.principalIdele K a)
        haIntegral hUnramified
  rw [← finitePlaceKummerRootCharacter_localGlobal K n hnK hmu v a b]
  unfold finitePlaceKummerRootCharacter
  unfold finitePlaceKummerRootCharacterOfExtension
  have hcomponent :
      (IdeleGroup.finiteComponent v (IdeleGroup.principalIdele K a) :
          (v.adicCompletion K)ˣ) =
        Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a := by
    apply Units.ext
    calc
      ((IdeleGroup.finiteComponent v (IdeleGroup.principalIdele K a) :
          (v.adicCompletion K)ˣ) : v.adicCompletion K) =
          ((a : K) : v.adicCompletion K) :=
        IdeleGroup.finiteComponent_principalIdele a v
      _ = algebraMap K (v.adicCompletion K) (a : K) := by
        symm
        have hmap := congrFun
          (IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion
            (R := 𝓞 K) (S := K) (K := K) (v := v)) (a : K)
        simpa using hmap
  rw [hcomponent] at hArtin
  unfold chosenFinitePlaceArtinMonoidHom at hArtin
  dsimp only at hArtin ⊢
  rw [hArtin, map_one, map_one]

open scoped Classical in
/-- Outside the concrete bad-place set, the finite-place Hilbert factor is
trivial. -/
theorem finitePlaceHilbertSymbol_eq_one_of_not_mem_powerResidueBadFinitePlaces
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : Kˣ) (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ powerResidueBadFinitePlaces K n a b) :
    finitePlaceHilbertSymbol K n hnK hmu v a b = 1 := by
  have hvaSupport : v ∉ chosenUnitFiniteSupport (K := K) a := by
    intro hva
    apply hv
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hva)
  have hvbSupport : v ∉ chosenUnitFiniteSupport (K := K) b := by
    intro hvb
    apply hv
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hvb)
  have hvnSupport :
      v ∉ powerResidueExponentFinitePlaces K n := by
    intro hvn
    apply hv
    exact Finset.mem_union_right _ hvn
  have hva : v.valuation K (a : K) = 1 :=
    valuation_eq_one_of_not_mem_chosenUnitFiniteSupport K a v hvaSupport
  have hvb : v.valuation K (b : K) = 1 :=
    valuation_eq_one_of_not_mem_chosenUnitFiniteSupport K b v hvbSupport
  have hvn : v.valuation K ((n : ℕ) : K) = 1 := by
    have hvnNotDvd :
        ¬ v.asIdeal ∣ powerResidueExponentIdeal K n := by
      simpa only [mem_powerResidueExponentFinitePlaces_iff] using hvnSupport
    have hvnNotMem : ((n : ℕ) : 𝓞 K) ∉ v.asIdeal := by
      intro hvnMem
      apply hvnNotDvd
      rw [powerResidueExponentIdeal, Ideal.dvd_span_singleton]
      exact hvnMem
    simpa only [map_natCast] using
      (v.valuation_eq_one_iff_notMem (K := K)
        (r := ((n : ℕ) : 𝓞 K))).2 hvnNotMem
  exact finitePlaceHilbertSymbol_eq_one_of_valuation_eq_one
    K n hnK hmu a b v hva hvb hvn

open scoped Classical in
/-- The multiplicative support of the finite-place Hilbert factors is
contained in the explicit power-residue bad-place set. -/
theorem finitePlaceHilbertSymbol_mulSupport_subset_powerResidueBadFinitePlaces
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : Kˣ) :
    Function.mulSupport
        (fun v : HeightOneSpectrum (𝓞 K) =>
          finitePlaceHilbertSymbol K n hnK hmu v a b) ⊆
      (powerResidueBadFinitePlaces K n a b :
        Set (HeightOneSpectrum (𝓞 K))) := by
  intro v hv
  change finitePlaceHilbertSymbol K n hnK hmu v a b ≠ 1 at hv
  change v ∈ powerResidueBadFinitePlaces K n a b
  by_contra hvBad
  exact hv
    (finitePlaceHilbertSymbol_eq_one_of_not_mem_powerResidueBadFinitePlaces
      K n hnK hmu a b v hvBad)

open scoped Classical in
/-- The finite-place Hilbert `finprod` is the ordinary product over the
explicit bad-place set. -/
theorem finitePlaceHilbertSymbol_finprod_eq_prod_powerResidueBadFinitePlaces
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : Kˣ) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 K),
        finitePlaceHilbertSymbol K n hnK hmu v a b) =
      ∏ v ∈ powerResidueBadFinitePlaces K n a b,
        finitePlaceHilbertSymbol K n hnK hmu v a b := by
  rw [finprod_eq_prod_of_mulSupport_subset _
    (finitePlaceHilbertSymbol_mulSupport_subset_powerResidueBadFinitePlaces
      K n hnK hmu a b)]

open scoped Classical in
/-- Finite-set form of the Hilbert product formula: the product over all
explicitly bad finite places is the inverse of the infinite-place product. -/
theorem powerResidueBadFinitePlaces_product_eq_infinitePlaceProduct_inv
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : Kˣ) :
    (∏ v ∈ powerResidueBadFinitePlaces K n a b,
        finitePlaceHilbertSymbol K n hnK hmu v a b) =
      (∏ v : InfinitePlace K,
        infinitePlaceHilbertSymbol K n v a b)⁻¹ := by
  have hproduct :=
    hilbertSymbol_allPlaces_product_eq_one K n hnK hmu a b
  rw [
    finitePlaceHilbertSymbol_finprod_eq_prod_powerResidueBadFinitePlaces]
      at hproduct
  exact (eq_inv_iff_mul_eq_one).2 (by
    simpa only [mul_comm] using hproduct)

open scoped Classical in
/-- The product of the finite-place Hilbert factors away from primes dividing
the exponent.  C1 identifies this term with the quotient of the two ideal
power-residue symbols; the remaining factors are exactly the correction. -/
noncomputable def powerResidueAwayFromExponentFiniteProduct
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : Kˣ) :
    nthRootsSubgroup K (n : ℕ) :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K),
    if v ∈ powerResidueExponentFinitePlaces K n then
      1
    else
      finitePlaceHilbertSymbol K n hnK hmu v a b

open scoped Classical in
/-- The complete tame finite-place product for two nonzero algebraic
integers is the quotient of the two ideal power-residue symbols. -/
theorem powerResidueAwayFromExponentFiniteProduct_integral_eq_idealSymbol_div
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : 𝓞 K) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hcoprimeA :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ Ideal.span {a} →
          (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (hcoprimeB :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ Ideal.span {b} →
          (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (haB :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ Ideal.span {b} → a ∉ P.asIdeal)
    (hbA :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ Ideal.span {a} → b ∉ P.asIdeal)
    (hAwayA :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ Ideal.span {a} →
          P ∉ powerResidueExponentFinitePlaces K n)
    (hAwayB :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ Ideal.span {b} →
          P ∉ powerResidueExponentFinitePlaces K n) :
    powerResidueAwayFromExponentFiniteProduct K n hnK hmu
        (nonzeroIntegralFieldUnit K a ha0)
        (nonzeroIntegralFieldUnit K b hb0) =
      integralRootsOfUnityToNthRoots K (n : ℕ)
          (idealPowerResidueSymbol K (Ideal.span {b})
            (ideal_span_singleton_ne_zero K hb0)
            n hmu a hcoprimeB haB) *
        (integralRootsOfUnityToNthRoots K (n : ℕ)
          (idealPowerResidueSymbol K (Ideal.span {a})
            (ideal_span_singleton_ne_zero K ha0)
            n hmu b hcoprimeA hbA))⁻¹ := by
  let IA : Ideal (𝓞 K) := Ideal.span {a}
  let IB : Ideal (𝓞 K) := Ideal.span {b}
  have hIA : IA ≠ 0 := by
    dsimp only [IA]
    exact ideal_span_singleton_ne_zero K ha0
  have hIB : IB ≠ 0 := by
    dsimp only [IB]
    exact ideal_span_singleton_ne_zero K hb0
  let fB : HeightOneSpectrum (𝓞 K) → nthRootsSubgroup K (n : ℕ) :=
    fun P => integralRootsOfUnityToNthRoots K (n : ℕ)
      (idealPowerResidueFactor K IB n hmu a hcoprimeB haB P)
  let fA : HeightOneSpectrum (𝓞 K) → nthRootsSubgroup K (n : ℕ) :=
    fun P => integralRootsOfUnityToNthRoots K (n : ℕ)
      (idealPowerResidueFactor K IA n hmu b hcoprimeA hbA P)
  have hfB : Function.HasFiniteMulSupport fB :=
    (idealPowerResidueFactor_hasFiniteMulSupport
      K IB hIB n hmu a hcoprimeB haB).subset (by
        intro P hP
        change fB P ≠ 1 at hP
        change idealPowerResidueFactor K IB n hmu a hcoprimeB haB P ≠ 1
        intro hOne
        exact hP (by simp only [fB, hOne, map_one]))
  have hfA : Function.HasFiniteMulSupport fA :=
    (idealPowerResidueFactor_hasFiniteMulSupport
      K IA hIA n hmu b hcoprimeA hbA).subset (by
        intro P hP
        change fA P ≠ 1 at hP
        change idealPowerResidueFactor K IA n hmu b hcoprimeA hbA P ≠ 1
        intro hOne
        exact hP (by simp only [fA, hOne, map_one]))
  have hfAInv :
      Function.HasFiniteMulSupport (fun P => (fA P)⁻¹) :=
    hfA.subset (by
      intro P hP
      change (fA P)⁻¹ ≠ 1 at hP
      change fA P ≠ 1
      intro hOne
      exact hP (by rw [hOne, inv_one]))
  let invHom : nthRootsSubgroup K (n : ℕ) →*
      nthRootsSubgroup K (n : ℕ) := invMonoidHom
  have hfinprodInv :
      (∏ᶠ P : HeightOneSpectrum (𝓞 K), (fA P)⁻¹) =
        (∏ᶠ P : HeightOneSpectrum (𝓞 K), fA P)⁻¹ := by
    change (∏ᶠ P : HeightOneSpectrum (𝓞 K), invHom (fA P)) =
      invHom (∏ᶠ P : HeightOneSpectrum (𝓞 K), fA P)
    exact (MonoidHom.map_finprod invHom hfA).symm
  calc
    powerResidueAwayFromExponentFiniteProduct K n hnK hmu
        (nonzeroIntegralFieldUnit K a ha0)
        (nonzeroIntegralFieldUnit K b hb0) =
        ∏ᶠ P : HeightOneSpectrum (𝓞 K), fB P * (fA P)⁻¹ := by
      apply finprod_congr
      intro P
      simpa only [fA, fB, IA, IB] using
        powerResidueAwayFromExponentFiniteFactor_integral_eq_idealFactors
          K n hnK hmu a b ha0 hb0 hcoprimeA hcoprimeB haB hbA
            hAwayA hAwayB P
    _ = (∏ᶠ P : HeightOneSpectrum (𝓞 K), fB P) *
        (∏ᶠ P : HeightOneSpectrum (𝓞 K), (fA P)⁻¹) :=
      finprod_mul_distrib hfB hfAInv
    _ = (∏ᶠ P : HeightOneSpectrum (𝓞 K), fB P) *
        (∏ᶠ P : HeightOneSpectrum (𝓞 K), fA P)⁻¹ := by
      rw [hfinprodInv]
    _ = integralRootsOfUnityToNthRoots K (n : ℕ)
          (idealPowerResidueSymbol K IB hIB n hmu a hcoprimeB haB) *
        (integralRootsOfUnityToNthRoots K (n : ℕ)
          (idealPowerResidueSymbol K IA hIA n hmu b hcoprimeA hbA))⁻¹ := by
      rw [idealPowerResidueSymbol_eq_finprod,
        idealPowerResidueSymbol_eq_finprod]
      rw [MonoidHom.map_finprod
          (integralRootsOfUnityToNthRoots K (n : ℕ))
          (idealPowerResidueFactor_hasFiniteMulSupport
            K IB hIB n hmu a hcoprimeB haB),
        MonoidHom.map_finprod
          (integralRootsOfUnityToNthRoots K (n : ℕ))
          (idealPowerResidueFactor_hasFiniteMulSupport
            K IA hIA n hmu b hcoprimeA hbA)]
    _ = integralRootsOfUnityToNthRoots K (n : ℕ)
          (idealPowerResidueSymbol K (Ideal.span {b})
            (ideal_span_singleton_ne_zero K hb0)
            n hmu a hcoprimeB haB) *
        (integralRootsOfUnityToNthRoots K (n : ℕ)
          (idealPowerResidueSymbol K (Ideal.span {a})
            (ideal_span_singleton_ne_zero K ha0)
            n hmu b hcoprimeA hbA))⁻¹ := by
      rfl

open scoped Classical in
/-- Split the full finite-place product into exponent-prime factors and the
product away from the exponent. -/
theorem finitePlaceHilbertSymbol_finprod_eq_exponent_product_mul_away
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : Kˣ) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 K),
        finitePlaceHilbertSymbol K n hnK hmu v a b) =
      (∏ v ∈ powerResidueExponentFinitePlaces K n,
          finitePlaceHilbertSymbol K n hnK hmu v a b) *
        powerResidueAwayFromExponentFiniteProduct K n hnK hmu a b := by
  let exponentFactor : HeightOneSpectrum (𝓞 K) →
      nthRootsSubgroup K (n : ℕ) := fun v =>
    if v ∈ powerResidueExponentFinitePlaces K n then
      finitePlaceHilbertSymbol K n hnK hmu v a b
    else
      1
  let awayFactor : HeightOneSpectrum (𝓞 K) →
      nthRootsSubgroup K (n : ℕ) := fun v =>
    if v ∈ powerResidueExponentFinitePlaces K n then
      1
    else
      finitePlaceHilbertSymbol K n hnK hmu v a b
  have hExponentSupport :
      Function.mulSupport exponentFactor ⊆
        (powerResidueExponentFinitePlaces K n :
          Set (HeightOneSpectrum (𝓞 K))) := by
    intro v hv
    change exponentFactor v ≠ 1 at hv
    change v ∈ powerResidueExponentFinitePlaces K n
    by_contra hvExponent
    exact hv (by simp only [exponentFactor, ite_eq_right hvExponent])
  have hExponentFinite : Function.HasFiniteMulSupport exponentFactor := by
    rw [Function.HasFiniteMulSupport]
    exact
      (powerResidueExponentFinitePlaces K n).finite_toSet.subset
        hExponentSupport
  have hAwayFinite : Function.HasFiniteMulSupport awayFactor := by
    rw [Function.HasFiniteMulSupport]
    exact
      (finitePlaceHilbertSymbol_hasFiniteMulSupport K n hnK hmu a b).subset
        (by
          intro v hv
          change awayFactor v ≠ 1 at hv
          change finitePlaceHilbertSymbol K n hnK hmu v a b ≠ 1
          by_contra hvOne
          exact hv (by simp only [awayFactor, hvOne, ite_self]))
  have hPointwise :
      (fun v : HeightOneSpectrum (𝓞 K) =>
        finitePlaceHilbertSymbol K n hnK hmu v a b) =
        fun v => exponentFactor v * awayFactor v := by
    funext v
    by_cases hv : v ∈ powerResidueExponentFinitePlaces K n
    · simp only [exponentFactor, awayFactor, ite_eq_left hv, mul_one]
    · simp only [exponentFactor, awayFactor, ite_eq_right hv, one_mul]
  have hExponentProduct :
      (∏ᶠ v : HeightOneSpectrum (𝓞 K), exponentFactor v) =
        ∏ v ∈ powerResidueExponentFinitePlaces K n,
          finitePlaceHilbertSymbol K n hnK hmu v a b := by
    rw [finprod_eq_prod_of_mulSupport_subset exponentFactor hExponentSupport]
    apply Finset.prod_congr rfl
    intro v hv
    simp only [exponentFactor, ite_eq_left hv]
  calc
    (∏ᶠ v : HeightOneSpectrum (𝓞 K),
        finitePlaceHilbertSymbol K n hnK hmu v a b) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          exponentFactor v * awayFactor v := by
      rw [hPointwise]
    _ = (∏ᶠ v : HeightOneSpectrum (𝓞 K), exponentFactor v) *
        (∏ᶠ v : HeightOneSpectrum (𝓞 K), awayFactor v) :=
      finprod_mul_distrib hExponentFinite hAwayFinite
    _ = (∏ v ∈ powerResidueExponentFinitePlaces K n,
          finitePlaceHilbertSymbol K n hnK hmu v a b) *
        (∏ᶠ v : HeightOneSpectrum (𝓞 K), awayFactor v) := by
      rw [hExponentProduct]
    _ = (∏ v ∈ powerResidueExponentFinitePlaces K n,
          finitePlaceHilbertSymbol K n hnK hmu v a b) *
        powerResidueAwayFromExponentFiniteProduct K n hnK hmu a b := by
      rfl

open scoped Classical in
/-- General Hilbert-product core of power-residue reciprocity.  The complete
finite product away from the exponent is the inverse of the explicit product
of all infinite-place factors and all exponent-prime factors. -/
theorem powerResidueAwayFromExponentFiniteProduct_eq_badPlaceCorrection_inv
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : Kˣ) :
    powerResidueAwayFromExponentFiniteProduct K n hnK hmu a b =
      (powerResidueBadPlaceCorrection K n hnK hmu a b)⁻¹ := by
  have hproduct :=
    hilbertSymbol_allPlaces_product_eq_one K n hnK hmu a b
  rw [finitePlaceHilbertSymbol_finprod_eq_exponent_product_mul_away]
      at hproduct
  exact (eq_inv_iff_mul_eq_one).2 (by
    unfold powerResidueBadPlaceCorrection
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hproduct)

open scoped Classical in
/-- General ideal power-residue reciprocity with the explicit product of
infinite and exponent-prime Hilbert factors as correction. -/
theorem idealPowerResidueSymbol_reciprocity_with_bad_place_correction
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : 𝓞 K) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hcoprimeA :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ Ideal.span {a} →
          (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (hcoprimeB :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ Ideal.span {b} →
          (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (haB :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ Ideal.span {b} → a ∉ P.asIdeal)
    (hbA :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ Ideal.span {a} → b ∉ P.asIdeal)
    (hAwayA :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ Ideal.span {a} →
          P ∉ powerResidueExponentFinitePlaces K n)
    (hAwayB :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ Ideal.span {b} →
          P ∉ powerResidueExponentFinitePlaces K n) :
    integralRootsOfUnityToNthRoots K (n : ℕ)
        (idealPowerResidueSymbol K (Ideal.span {b})
          (ideal_span_singleton_ne_zero K hb0)
          n hmu a hcoprimeB haB) =
      (powerResidueBadPlaceCorrection K n hnK hmu
        (nonzeroIntegralFieldUnit K a ha0)
        (nonzeroIntegralFieldUnit K b hb0))⁻¹ *
      integralRootsOfUnityToNthRoots K (n : ℕ)
        (idealPowerResidueSymbol K (Ideal.span {a})
          (ideal_span_singleton_ne_zero K ha0)
          n hmu b hcoprimeA hbA) := by
  let symbolAB := integralRootsOfUnityToNthRoots K (n : ℕ)
    (idealPowerResidueSymbol K (Ideal.span {b})
      (ideal_span_singleton_ne_zero K hb0)
      n hmu a hcoprimeB haB)
  let symbolBA := integralRootsOfUnityToNthRoots K (n : ℕ)
    (idealPowerResidueSymbol K (Ideal.span {a})
      (ideal_span_singleton_ne_zero K ha0)
      n hmu b hcoprimeA hbA)
  let correction := powerResidueBadPlaceCorrection K n hnK hmu
    (nonzeroIntegralFieldUnit K a ha0)
    (nonzeroIntegralFieldUnit K b hb0)
  have hIdeal :=
    powerResidueAwayFromExponentFiniteProduct_integral_eq_idealSymbol_div
      K n hnK hmu a b ha0 hb0 hcoprimeA hcoprimeB haB hbA
        hAwayA hAwayB
  have hCorrection :=
    powerResidueAwayFromExponentFiniteProduct_eq_badPlaceCorrection_inv
      K n hnK hmu
        (nonzeroIntegralFieldUnit K a ha0)
        (nonzeroIntegralFieldUnit K b hb0)
  have hQuotient : symbolAB * symbolBA⁻¹ = correction⁻¹ := by
    rw [← hIdeal, hCorrection]
  change symbolAB = correction⁻¹ * symbolBA
  calc
    symbolAB = (symbolAB * symbolBA⁻¹) * symbolBA := by
      simp only [mul_assoc, inv_mul_cancel, mul_one]
    _ = correction⁻¹ * symbolBA := by rw [hQuotient]

/-! ## Quadratic specialization over the rational field -/

open AlgebraicNumberTheory.PowerResidueSymbols

open scoped Classical in
local instance rationalPrimeFact (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

attribute [local instance] rationalPrimeFact

open scoped Classical in
/-- The rational field contains the primitive square root of unity `-1`.
This is the canonical source of the primitive-root input in the quadratic
specialization; no root is chosen downstream. -/
theorem rationalQuadraticPrimitiveRoots_nonempty :
    (primitiveRoots 2 ℚ).Nonempty := by
  refine ⟨-1, (mem_primitiveRoots (by decide)).2 ?_⟩
  exact IsPrimitiveRoot.neg_one 0 (by decide)

open scoped Classical in
/-- The residue field at the rational prime over `p` is canonically `ZMod p`.
The construction first transports the prime ideal through
`Rat.ringOfIntegersEquiv` and then uses the standard integer quotient. -/
noncomputable def rationalPrimeResidueEquivZMod
    (p : Nat.Primes) :
    (𝓞 ℚ ⧸ (RayClass.rationalPrime p).asIdeal) ≃+* ZMod p.1 := by
  have hIntEquiv :
      Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) =
        Rat.ringOfIntegersEquiv := by
    ext x
    exact Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv x
  have hmap :
      Ideal.span {(p.1 : ℤ)} =
        (RayClass.rationalPrime p).asIdeal.map
          Rat.ringOfIntegersEquiv := by
    simpa only [RayClass.natGenerator_rationalPrime, hIntEquiv] using
      (Rat.HeightOneSpectrum.span_natGenerator
        (RayClass.rationalPrime p))
  exact
    (Ideal.quotientEquiv
      (RayClass.rationalPrime p).asIdeal
      (Ideal.span {(p.1 : ℤ)})
      Rat.ringOfIntegersEquiv hmap).trans
        (Int.quotientSpanNatEquivZMod p.1)

open scoped Classical in
/-- The rational residue-field equivalence sends an integral residue class to
the corresponding integer class modulo `p`. -/
@[simp]
theorem rationalPrimeResidueEquivZMod_mk
    (p : Nat.Primes) (a : 𝓞 ℚ) :
    rationalPrimeResidueEquivZMod p
      (Ideal.Quotient.mk (RayClass.rationalPrime p).asIdeal a) =
      (Rat.ringOfIntegersEquiv a : ZMod p.1) := by
  rw [rationalPrimeResidueEquivZMod, RingEquiv.trans_apply]
  have hmk
      (hIJ :
        Ideal.span {(p.1 : ℤ)} =
          (RayClass.rationalPrime p).asIdeal.map
            Rat.ringOfIntegersEquiv) :
      Ideal.quotientEquiv
          (RayClass.rationalPrime p).asIdeal
          (Ideal.span {(p.1 : ℤ)})
          Rat.ringOfIntegersEquiv hIJ
          (Ideal.Quotient.mk (RayClass.rationalPrime p).asIdeal a) =
        Ideal.Quotient.mk (Ideal.span {(p.1 : ℤ)})
          (Rat.ringOfIntegersEquiv a) :=
    Ideal.quotientEquiv_mk
      (RayClass.rationalPrime p).asIdeal
      (Ideal.span {(p.1 : ℤ)})
      Rat.ringOfIntegersEquiv hIJ a
  have hquot :
      ((Int.quotientSpanNatEquivZMod p.1 :
          (ℤ ⧸ Ideal.span {(p.1 : ℤ)}) →+* ZMod p.1).comp
        (Ideal.Quotient.mk (Ideal.span {(p.1 : ℤ)}))) =
        Int.castRingHom (ZMod p.1) :=
    Int.quotientSpanNatEquivZMod_comp_Quotient_mk p.1
  calc
    _ = Int.quotientSpanNatEquivZMod p.1
        (Ideal.Quotient.mk (Ideal.span {(p.1 : ℤ)})
          (Rat.ringOfIntegersEquiv a)) :=
      congrArg (Int.quotientSpanNatEquivZMod p.1) (hmk _)
    _ = _ := congrArg
      (fun f : ℤ →+* ZMod p.1 => f (Rat.ringOfIntegersEquiv a)) hquot

open scoped Classical in
/-- The absolute norm of the rational prime ideal attached to `p` is `p`.
This follows from the explicit residue-field equivalence rather than from a
cardinality assumption supplied by a consumer. -/
theorem absNorm_rationalPrime (p : Nat.Primes) :
    Ideal.absNorm (RayClass.rationalPrime p).asIdeal = p.1 := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  calc
    Nat.card (𝓞 ℚ ⧸ (RayClass.rationalPrime p).asIdeal) =
        Nat.card (ZMod p.1) :=
      Nat.card_congr (rationalPrimeResidueEquivZMod p).toEquiv
    _ = p.1 := Nat.card_zmod p.1

open scoped Classical in
/-- An odd rational prime has residue characteristic coprime to the quadratic
exponent. -/
theorem absNorm_rationalPrime_coprime_two
    (p : Nat.Primes) (hp : p.1 ≠ 2) :
    (Ideal.absNorm (RayClass.rationalPrime p).asIdeal).Coprime 2 := by
  rw [absNorm_rationalPrime]
  exact (p.2.odd_of_ne_two hp).coprime_two_right

open scoped Classical in
/-- Evaluate a quadratic integral root of unity as the corresponding integer
sign. -/
def rationalQuadraticRootValue
    (z : rootsOfUnity 2 (𝓞 ℚ)) : ℤ :=
  Rat.ringOfIntegersEquiv (z.1 : 𝓞 ℚ)

open scoped Classical in
/-- The identity quadratic root evaluates to the positive integer sign. -/
@[simp]
theorem rationalQuadraticRootValue_one :
    rationalQuadraticRootValue (1 : rootsOfUnity 2 (𝓞 ℚ)) = 1 := by
  simp [rationalQuadraticRootValue]

open scoped Classical in
/-- Integer evaluation of quadratic roots of unity is multiplicative. -/
def rationalQuadraticRootValueMonoidHom :
    rootsOfUnity 2 (𝓞 ℚ) →* ℤ where
  toFun := rationalQuadraticRootValue
  map_one' := rationalQuadraticRootValue_one
  map_mul' := by
    intro z w
    simp [rationalQuadraticRootValue]

open scoped Classical in
/-- The multiplicative sign evaluation has the expected underlying function. -/
@[simp]
theorem rationalQuadraticRootValueMonoidHom_apply
    (z : rootsOfUnity 2 (𝓞 ℚ)) :
    rationalQuadraticRootValueMonoidHom z =
      rationalQuadraticRootValue z :=
  rfl

open scoped Classical in
/-- The integer sign evaluation detects the identity root. -/
theorem rationalQuadraticRootValue_eq_one_iff
    (z : rootsOfUnity 2 (𝓞 ℚ)) :
    rationalQuadraticRootValue z = 1 ↔ z = 1 := by
  constructor
  · intro hz
    apply Subtype.ext
    apply Units.ext
    apply Rat.ringOfIntegersEquiv.injective
    change Rat.ringOfIntegersEquiv (z.1 : 𝓞 ℚ) =
      Rat.ringOfIntegersEquiv (1 : 𝓞 ℚ)
    rw [map_one]
    simpa only [rationalQuadraticRootValue] using hz
  · rintro rfl
    exact rationalQuadraticRootValue_one

open scoped Classical in
/-- A quadratic root evaluates to one of the two integer signs. -/
theorem rationalQuadraticRootValue_eq_one_or_neg_one
    (z : rootsOfUnity 2 (𝓞 ℚ)) :
    rationalQuadraticRootValue z = 1 ∨
      rationalQuadraticRootValue z = -1 := by
  have hzUnits : z.1 ^ 2 = 1 := z.2
  have hzIntegers : ((z.1 : 𝓞 ℚ) ^ 2) = 1 := by
    simpa using congrArg (fun u : (𝓞 ℚ)ˣ ↦ (u : 𝓞 ℚ)) hzUnits
  have hzSign := congrArg Rat.ringOfIntegersEquiv hzIntegers
  have hzSquare : rationalQuadraticRootValue z ^ 2 = 1 := by
    simpa only [rationalQuadraticRootValue, map_pow, map_one] using hzSign
  exact (sq_eq_one_iff).mp hzSquare

open scoped Classical in
/-- The chosen integral numerator remains nonzero after passing to the
standard residue field `ZMod p`. -/
theorem rationalPrimeResidue_intCast_ne_zero
    (p : Nat.Primes) (a : 𝓞 ℚ)
    (ha : a ∉ (RayClass.rationalPrime p).asIdeal) :
    (Rat.ringOfIntegersEquiv a : ZMod p.1) ≠ 0 := by
  intro haz
  apply ha
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply (rationalPrimeResidueEquivZMod p).injective
  simpa only [rationalPrimeResidueEquivZMod_mk, map_zero] using haz

open scoped Classical in
/-- A square among residue units is exactly a square in the standard rational
prime residue field.  The reverse implication constructs the unit from the
nonzero square root. -/
theorem rationalPrimeResidueUnit_sq_iff_isSquare
    (p : Nat.Primes) (a : 𝓞 ℚ)
    (ha : a ∉ (RayClass.rationalPrime p).asIdeal) :
    (∃ u : (𝓞 ℚ ⧸ (RayClass.rationalPrime p).asIdeal)ˣ,
        u ^ 2 = primeIdealResidueUnit ℚ (RayClass.rationalPrime p) a ha) ↔
      IsSquare (Rat.ringOfIntegersEquiv a : ZMod p.1) := by
  let e := rationalPrimeResidueEquivZMod p
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨e (u : 𝓞 ℚ ⧸ (RayClass.rationalPrime p).asIdeal), ?_⟩
    have hu' := congrArg
      (fun x : (𝓞 ℚ ⧸ (RayClass.rationalPrime p).asIdeal)ˣ ↦
        e (x : 𝓞 ℚ ⧸ (RayClass.rationalPrime p).asIdeal)) hu
    simpa [e, pow_two, primeIdealResidueUnit,
      rationalPrimeResidueEquivZMod_mk] using hu'.symm
  · rintro ⟨x, hx⟩
    have haZ : (Rat.ringOfIntegersEquiv a : ZMod p.1) ≠ 0 :=
      rationalPrimeResidue_intCast_ne_zero p a ha
    have hxne : x ≠ 0 := by
      intro hxzero
      apply haZ
      simpa [hxzero] using hx
    let u : (𝓞 ℚ ⧸ (RayClass.rationalPrime p).asIdeal)ˣ :=
      Units.map e.symm.toRingHom (Units.mk0 x hxne)
    refine ⟨u, ?_⟩
    apply Units.ext
    apply e.injective
    simpa [u, e, pow_two, primeIdealResidueUnit,
      rationalPrimeResidueEquivZMod_mk] using hx.symm

open scoped Classical in
/-- The quadratic prime-ideal power-residue symbol over `ℚ`, evaluated as an
integer sign, is the classical Legendre symbol. -/
theorem rationalPrimeIdealPowerResidueSymbol_two_eq_legendre
    (p : Nat.Primes) (hp : p.1 ≠ 2)
    (a : 𝓞 ℚ) (ha : a ∉ (RayClass.rationalPrime p).asIdeal) :
    rationalQuadraticRootValue
        (primeIdealPowerResidueSymbol ℚ (RayClass.rationalPrime p)
          (2 : ℕ+) rationalQuadraticPrimitiveRoots_nonempty
          (absNorm_rationalPrime_coprime_two p hp) a ha) =
      legendreSym p.1 (Rat.ringOfIntegersEquiv a) := by
  let z :=
    primeIdealPowerResidueSymbol ℚ (RayClass.rationalPrime p)
      (2 : ℕ+) rationalQuadraticPrimitiveRoots_nonempty
      (absNorm_rationalPrime_coprime_two p hp) a ha
  have haZ : (Rat.ringOfIntegersEquiv a : ZMod p.1) ≠ 0 :=
    rationalPrimeResidue_intCast_ne_zero p a ha
  have hzOne : z = 1 ↔ legendreSym p.1 (Rat.ringOfIntegersEquiv a) = 1 := by
    calc
      z = 1 ↔
          ∃ u : (𝓞 ℚ ⧸ (RayClass.rationalPrime p).asIdeal)ˣ,
            u ^ 2 = primeIdealResidueUnit ℚ
              (RayClass.rationalPrime p) a ha :=
        primeIdealPowerResidueSymbol_eq_one_iff ℚ
          (RayClass.rationalPrime p) (2 : ℕ+)
          rationalQuadraticPrimitiveRoots_nonempty
          (absNorm_rationalPrime_coprime_two p hp) a ha
      _ ↔ IsSquare (Rat.ringOfIntegersEquiv a : ZMod p.1) :=
        rationalPrimeResidueUnit_sq_iff_isSquare p a ha
      _ ↔ legendreSym p.1 (Rat.ringOfIntegersEquiv a) = 1 :=
        (legendreSym.eq_one_iff p.1 haZ).symm
  rcases rationalQuadraticRootValue_eq_one_or_neg_one z with hz | hz
  · have hzRoot : z = 1 :=
      (rationalQuadraticRootValue_eq_one_iff z).1 hz
    calc
      rationalQuadraticRootValue z = 1 := hz
      _ = legendreSym p.1 (Rat.ringOfIntegersEquiv a) :=
        (hzOne.1 hzRoot).symm
  · rcases legendreSym.eq_one_or_neg_one p.1 haZ with hleg | hleg
    · have hzRoot : z = 1 := hzOne.2 hleg
      have hzValue : rationalQuadraticRootValue z = 1 :=
        (rationalQuadraticRootValue_eq_one_iff z).2 hzRoot
      have hcontr : (1 : ℤ) = -1 := hzValue.symm.trans hz
      norm_num at hcontr
    · exact hz.trans hleg.symm

/-! ## Rational principal-ideal factorization -/

open scoped Classical in
/-- The principal ideal of `𝓞 ℚ` generated by a natural number, expressed
through the canonical equivalence `𝓞 ℚ ≃+* ℤ`. -/
noncomputable def rationalPrincipalIdeal (b : ℕ) : Ideal (𝓞 ℚ) :=
  Ideal.span {Rat.ringOfIntegersEquiv.symm (b : ℤ)}

open scoped Classical in
/-- A positive rational principal ideal is nonzero. -/
theorem rationalPrincipalIdeal_ne_zero
    (b : ℕ) (hb : b ≠ 0) :
    rationalPrincipalIdeal b ≠ 0 := by
  unfold rationalPrincipalIdeal
  apply ideal_span_singleton_ne_zero ℚ
  have hbInt : (b : ℤ) ≠ 0 := Int.ofNat_ne_zero.mpr hb
  have h := Rat.ringOfIntegersEquiv.symm.injective.ne hbInt
  simpa only [map_zero] using h

open scoped Classical in
/-- The height-one prime of `𝓞 ℚ` attached to `p` is generated by the
corresponding rational integer. -/
theorem rationalPrime_asIdeal_eq_span
    (p : Nat.Primes) :
    (RayClass.rationalPrime p).asIdeal =
      Ideal.span {Rat.ringOfIntegersEquiv.symm (p.1 : ℤ)} := by
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    RayClass.rationalPrime p
  have hIntEquiv :
      Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) =
        Rat.ringOfIntegersEquiv := by
    ext x
    exact
      Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv x
  have hspan :
      Ideal.span {(p.1 : ℤ)} =
        v.asIdeal.map Rat.ringOfIntegersEquiv := by
    simpa only [v, RayClass.natGenerator_rationalPrime,
      hIntEquiv] using
      Rat.HeightOneSpectrum.span_natGenerator v
  apply
    ((RingEquiv.idealComapOrderIso
      Rat.ringOfIntegersEquiv).symm).injective
  simp only [RingEquiv.idealComapOrderIso_symm_apply]
  calc
    (RayClass.rationalPrime p).asIdeal.map
          Rat.ringOfIntegersEquiv =
        Ideal.span {(p.1 : ℤ)} := by
      simpa only [v] using hspan.symm
    _ =
      (Ideal.span
          {Rat.ringOfIntegersEquiv.symm (p.1 : ℤ)}).map
            Rat.ringOfIntegersEquiv := by
      rw [Ideal.map_span, Set.image_singleton,
        Rat.ringOfIntegersEquiv.apply_symm_apply]

open scoped Classical in
/-- Divisibility of a rational principal ideal by the prime over `p` is
exactly natural-number divisibility by `p`. -/
theorem rationalPrime_dvd_rationalPrincipalIdeal_iff
    (p : Nat.Primes) (b : ℕ) :
    (RayClass.rationalPrime p).asIdeal ∣ rationalPrincipalIdeal b ↔
      p.1 ∣ b := by
  rw [rationalPrincipalIdeal, rationalPrime_asIdeal_eq_span,
    Ideal.dvd_iff_le, Ideal.span_singleton_le_span_singleton,
    map_dvd_iff Rat.ringOfIntegersEquiv.symm,
    Int.natCast_dvd_natCast]

open scoped Classical in
/-- Every prime divisor of an odd rational principal ideal has odd residue
characteristic.  Thus its norm is coprime to the quadratic exponent. -/
theorem rationalPrincipalIdeal_absNorm_coprime_two_of_odd
    (b : ℕ) (hbOdd : Odd b)
    (P : HeightOneSpectrum (𝓞 ℚ))
    (hP : P.asIdeal ∣ rationalPrincipalIdeal b) :
    (Ideal.absNorm P.asIdeal).Coprime 2 := by
  let p : Nat.Primes :=
    ⟨Rat.HeightOneSpectrum.natGenerator P,
      Rat.HeightOneSpectrum.prime_natGenerator P⟩
  have hprimeEq : RayClass.rationalPrime p = P := by
    exact
      (Rat.HeightOneSpectrum.primesEquiv
        (R := 𝓞 ℚ)).symm_apply_apply P
  have hpIdealDvd :
      (RayClass.rationalPrime p).asIdeal ∣
        rationalPrincipalIdeal b := by
    rw [hprimeEq]
    exact hP
  have hpDvd : p.1 ∣ b :=
    (rationalPrime_dvd_rationalPrincipalIdeal_iff p b).mp hpIdealDvd
  have hpNeTwo : p.1 ≠ 2 := by
    intro hpTwo
    apply hbOdd.not_two_dvd_nat
    simpa only [hpTwo] using hpDvd
  rw [← hprimeEq]
  exact absNorm_rationalPrime_coprime_two p hpNeTwo

open scoped Classical in
/-- Coprimality of the integer numerator and the natural denominator excludes
the numerator from every prime ideal dividing the denominator ideal. -/
theorem rationalPrincipalIdeal_numerator_not_mem_of_coprime
    (a : 𝓞 ℚ) (b : ℕ)
    (hab : Nat.Coprime
      (Rat.ringOfIntegersEquiv a).natAbs b)
    (P : HeightOneSpectrum (𝓞 ℚ))
    (hP : P.asIdeal ∣ rationalPrincipalIdeal b) :
    a ∉ P.asIdeal := by
  intro haP
  let p : Nat.Primes :=
    ⟨Rat.HeightOneSpectrum.natGenerator P,
      Rat.HeightOneSpectrum.prime_natGenerator P⟩
  have hprimeEq : RayClass.rationalPrime p = P := by
    exact
      (Rat.HeightOneSpectrum.primesEquiv
        (R := 𝓞 ℚ)).symm_apply_apply P
  have hpIdealDvd :
      (RayClass.rationalPrime p).asIdeal ∣
        rationalPrincipalIdeal b := by
    rw [hprimeEq]
    exact hP
  have hpDvdB : p.1 ∣ b :=
    (rationalPrime_dvd_rationalPrincipalIdeal_iff p b).mp hpIdealDvd
  have hpCoprimeA :
      Nat.Coprime p.1 (Rat.ringOfIntegersEquiv a).natAbs :=
    (hab.of_dvd_right hpDvdB).symm
  have hpNotDvdA :
      ¬ p.1 ∣ (Rat.ringOfIntegersEquiv a).natAbs :=
    p.2.coprime_iff_not_dvd.mp hpCoprimeA
  apply hpNotDvdA
  have haPrime :
      a ∈ (RayClass.rationalPrime p).asIdeal := by
    rw [hprimeEq]
    exact haP
  rw [rationalPrime_asIdeal_eq_span,
    Ideal.mem_span_singleton] at haPrime
  have hpDvdInt :
      (p.1 : ℤ) ∣ Rat.ringOfIntegersEquiv a := by
    apply (map_dvd_iff Rat.ringOfIntegersEquiv.symm).mp
    simpa only [Rat.ringOfIntegersEquiv.symm_apply_apply] using haPrime
  exact Int.natCast_dvd.mp hpDvdInt

open scoped Classical in
/-- The multiplicity of the rational prime ideal over `p` in `(b)` is the
usual `p`-adic exponent in the natural-number factorization of `b`. -/
theorem idealPrimeMultiplicity_rationalPrincipalIdeal
    (p : Nat.Primes) (b : ℕ) (hb : b ≠ 0) :
    idealPrimeMultiplicity ℚ (RayClass.rationalPrime p)
        (rationalPrincipalIdeal b) =
      b.factorization p.1 := by
  let e := Rat.ringOfIntegersEquiv
  let x : 𝓞 ℚ := e.symm (p.1 : ℤ)
  let a : 𝓞 ℚ := e.symm (b : ℤ)
  have hpInt : Prime (p.1 : ℤ) :=
    Int.prime_iff_natAbs_prime.mpr (by simpa using p.2)
  have hxPrime : Prime x := by
    exact (MulEquiv.prime_iff e.symm).mpr hpInt
  have hpow : x ^ b.factorization p.1 ∣ a := by
    have hpowNat : p.1 ^ b.factorization p.1 ∣ b :=
      (p.2.pow_dvd_iff_le_factorization hb).mpr le_rfl
    have hpowInt :
        (p.1 : ℤ) ^ b.factorization p.1 ∣ (b : ℤ) := by
      exact_mod_cast hpowNat
    simpa only [x, a, ← map_pow,
      map_dvd_iff e.symm] using hpowInt
  have hpowSucc : ¬x ^ (b.factorization p.1 + 1) ∣ a := by
    intro h
    have hInt :
        (p.1 : ℤ) ^ (b.factorization p.1 + 1) ∣ (b : ℤ) := by
      simpa only [x, a, ← map_pow,
        map_dvd_iff e.symm] using h
    have hNat : p.1 ^ (b.factorization p.1 + 1) ∣ b := by
      exact_mod_cast hInt
    have hle := (p.2.pow_dvd_iff_le_factorization hb).mp hNat
    omega
  rw [idealPrimeMultiplicity, rationalPrincipalIdeal,
    rationalPrime_asIdeal_eq_span]
  simpa only [x, a] using
    (Ideal.count_associates_eq' hxPrime hpow hpowSucc)

open scoped Classical in
/-- Prime divisors of the rational principal ideal `(b)` are canonically the
natural prime factors of `b`. -/
noncomputable def rationalPrincipalIdealPrimeDivisorsEquiv
    (b : ℕ) (hb : b ≠ 0) :
    idealPrimeDivisors ℚ (rationalPrincipalIdeal b) ≃
      b.primeFactors where
  toFun P :=
    ⟨Rat.HeightOneSpectrum.natGenerator P.1,
      (Nat.mem_primeFactors_of_ne_zero hb).mpr
        ⟨Rat.HeightOneSpectrum.prime_natGenerator P.1,
            (rationalPrime_dvd_rationalPrincipalIdeal_iff
            ⟨Rat.HeightOneSpectrum.natGenerator P.1,
              Rat.HeightOneSpectrum.prime_natGenerator P.1⟩ b).mp
            (by
              have hprimeEq :
                  RayClass.rationalPrime
                      ⟨Rat.HeightOneSpectrum.natGenerator P.1,
                        Rat.HeightOneSpectrum.prime_natGenerator P.1⟩ =
                    P.1 :=
                (Rat.HeightOneSpectrum.primesEquiv
                  (R := 𝓞 ℚ)).symm_apply_apply P.1
              rw [hprimeEq]
              exact P.2)⟩⟩
  invFun p :=
    ⟨RayClass.rationalPrime
        ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩,
      (rationalPrime_dvd_rationalPrincipalIdeal_iff
        ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ b).mpr
        (Nat.dvd_of_mem_primeFactors p.2)⟩
  left_inv P := by
    apply Subtype.ext
    have hq :
        (⟨Rat.HeightOneSpectrum.natGenerator P.1,
          Rat.HeightOneSpectrum.prime_natGenerator P.1⟩ : Nat.Primes) =
          Rat.HeightOneSpectrum.primesEquiv P.1 :=
      Subtype.ext rfl
    simpa only [RayClass.rationalPrime, hq] using
      (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm_apply_apply P.1
  right_inv p := by
    apply Subtype.ext
    exact
      RayClass.natGenerator_rationalPrime
        ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩

open scoped Classical in
/-- Reindexing a natural prime factor back to a height-one prime gives the
standard rational prime above it. -/
@[simp]
theorem rationalPrincipalIdealPrimeDivisorsEquiv_symm_apply_val
    (b : ℕ) (hb : b ≠ 0) (p : b.primeFactors) :
    ((rationalPrincipalIdealPrimeDivisorsEquiv b hb).symm p).1 =
      RayClass.rationalPrime
        ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ :=
  rfl

open scoped Classical in
/-- Under the prime-factor reindexing, ideal multiplicity becomes the
corresponding entry of `Nat.factorization`. -/
theorem idealPrimeMultiplicity_rationalPrincipalIdeal_reindexed
    (b : ℕ) (hb : b ≠ 0) (p : b.primeFactors) :
    idealPrimeMultiplicity ℚ
        ((rationalPrincipalIdealPrimeDivisorsEquiv b hb).symm p).1
        (rationalPrincipalIdeal b) =
      b.factorization p.1 := by
  rw [rationalPrincipalIdealPrimeDivisorsEquiv_symm_apply_val b hb p]
  exact idealPrimeMultiplicity_rationalPrincipalIdeal
    ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ b hb

open scoped Classical in
/-- Reindex a product over the prime divisors of `(b)` by the ordinary
natural prime factors of `b`. -/
theorem prod_rationalPrincipalIdealPrimeDivisors_eq_prod_primeFactors
    {M : Type*} [CommMonoid M]
    (b : ℕ) (hb : b ≠ 0)
    (f : HeightOneSpectrum (𝓞 ℚ) → M) :
    letI : Fintype
        (idealPrimeDivisors ℚ (rationalPrincipalIdeal b)) :=
      (idealPrimeDivisors_finite ℚ (rationalPrincipalIdeal b)
        (rationalPrincipalIdeal_ne_zero b hb)).fintype
    (∏ P : idealPrimeDivisors ℚ (rationalPrincipalIdeal b), f P.1) =
      ∏ p : b.primeFactors,
        f ((rationalPrincipalIdealPrimeDivisorsEquiv b hb).symm p).1 := by
  let : Fintype
      (idealPrimeDivisors ℚ (rationalPrincipalIdeal b)) :=
    (idealPrimeDivisors_finite ℚ (rationalPrincipalIdeal b)
      (rationalPrincipalIdeal_ne_zero b hb)).fintype
  exact
    Fintype.prod_equiv
      (rationalPrincipalIdealPrimeDivisorsEquiv b hb)
      (fun P => f P.1)
      (fun p => f ((rationalPrincipalIdealPrimeDivisorsEquiv b hb).symm p).1)
      (fun P => by
        rw [(rationalPrincipalIdealPrimeDivisorsEquiv b hb).symm_apply_apply])

open scoped Classical in
/-- Reindex a product whose factor also depends on the divisibility witness.
This is the subtype-valued form used by the defining product of the ideal
power-residue symbol. -/
theorem prod_rationalPrincipalIdealPrimeDivisors_eq_prod_primeFactors_subtype
    {M : Type*} [CommMonoid M]
    (b : ℕ) (hb : b ≠ 0)
    (f : idealPrimeDivisors ℚ (rationalPrincipalIdeal b) → M) :
    letI : Fintype
        (idealPrimeDivisors ℚ (rationalPrincipalIdeal b)) :=
      (idealPrimeDivisors_finite ℚ (rationalPrincipalIdeal b)
        (rationalPrincipalIdeal_ne_zero b hb)).fintype
    (∏ P : idealPrimeDivisors ℚ (rationalPrincipalIdeal b), f P) =
      ∏ p : b.primeFactors,
        f ((rationalPrincipalIdealPrimeDivisorsEquiv b hb).symm p) := by
  let : Fintype
      (idealPrimeDivisors ℚ (rationalPrincipalIdeal b)) :=
    (idealPrimeDivisors_finite ℚ (rationalPrincipalIdeal b)
      (rationalPrincipalIdeal_ne_zero b hb)).fintype
  exact
    Fintype.prod_equiv
      (rationalPrincipalIdealPrimeDivisorsEquiv b hb)
      f
      (fun p =>
        f ((rationalPrincipalIdealPrimeDivisorsEquiv b hb).symm p))
      (fun P => by
        rw [(rationalPrincipalIdealPrimeDivisorsEquiv b hb).symm_apply_apply])

open scoped Classical in
/-- The list-based Jacobi symbol is the product over distinct prime factors,
with the usual natural factorization multiplicity as exponent. -/
theorem jacobiSym_eq_prod_primeFactors_factorization
    (a : ℤ) (b : ℕ) :
    jacobiSym a b =
      ∏ p : b.primeFactors,
        (@legendreSym p.1
          ⟨Nat.prime_of_mem_primeFactors p.2⟩ a) ^
          b.factorization p.1 := by
  let f : ℕ → ℤ := fun p =>
    if hp : p.Prime then @legendreSym p ⟨hp⟩ a else 1
  rw [jacobiSym]
  have hmap :
      b.primeFactorsList.pmap
          (fun p pp => @legendreSym p ⟨pp⟩ a)
          (fun _ hp => Nat.prime_of_mem_primeFactorsList hp) =
        b.primeFactorsList.map f := by
    rw [← List.pmap_eq_map
      (fun _ hp => Nat.prime_of_mem_primeFactorsList hp)]
    apply List.pmap_congr_left
    intro p hp hprime _
    simp only [f, dite_eq_left hprime]
  rw [hmap, Finset.prod_list_map_count]
  have hrhs :
      (∏ p : b.primeFactors,
          (@legendreSym p.1
            ⟨Nat.prime_of_mem_primeFactors p.2⟩ a) ^
            b.factorization p.1) =
        ∏ p : b.primeFactors, f p.1 ^ b.factorization p.1 := by
    apply Fintype.prod_congr
    intro p
    have hpPrime : p.1.Prime :=
      Nat.prime_of_mem_primeFactors p.2
    simp only [f, dite_eq_left hpPrime]
  rw [hrhs]
  calc
    _ = ∏ p ∈ b.primeFactors,
        f p ^ b.factorization p := by
      apply Finset.prod_congr rfl
      intro p hp
      simp only [Nat.primeFactorsList_count_eq]
    _ = ∏ p : b.primeFactors,
        f p.1 ^ b.factorization p.1 :=
      (Finset.prod_coe_sort b.primeFactors
        (fun p => f p ^ b.factorization p)).symm

open scoped Classical in
private theorem rationalQuadraticPrimitiveRoots_nonempty_pnat :
    (primitiveRoots (((2 : ℕ+) : ℕ)) ℚ).Nonempty := by
  change (primitiveRoots 2 ℚ).Nonempty
  exact rationalQuadraticPrimitiveRoots_nonempty

open scoped Classical in
private def rationalQuadraticRootValuePNatMonoidHom :
    rootsOfUnity (((2 : ℕ+) : ℕ)) (𝓞 ℚ) →* ℤ := by
  change rootsOfUnity 2 (𝓞 ℚ) →* ℤ
  exact rationalQuadraticRootValueMonoidHom

open scoped Classical in
private noncomputable def rationalIdealQuadraticSourceFactor
    (a : 𝓞 ℚ) (b : ℕ) (hbOdd : Odd b)
    (hab : Nat.Coprime (Rat.ringOfIntegersEquiv a).natAbs b)
    (P : idealPrimeDivisors ℚ (rationalPrincipalIdeal b)) : ℤ :=
  Rat.ringOfIntegersEquiv
    ((primeIdealPowerResidueSymbol ℚ P.1 (2 : ℕ+)
        rationalQuadraticPrimitiveRoots_nonempty_pnat
        (by
          change
            (Ideal.absNorm P.1.asIdeal).Coprime 2
          exact rationalPrincipalIdeal_absNorm_coprime_two_of_odd
            b hbOdd P.1
              ((mem_idealPrimeDivisors ℚ (rationalPrincipalIdeal b) P.1).mp P.2))
        a
        (rationalPrincipalIdeal_numerator_not_mem_of_coprime
          a b hab P.1
            ((mem_idealPrimeDivisors ℚ (rationalPrincipalIdeal b) P.1).mp P.2))).1.1 ^
      idealPrimeMultiplicity ℚ P.1 (rationalPrincipalIdeal b))

open scoped Classical in
private def rationalJacobiPrimeFactor
    (a : 𝓞 ℚ) (b : ℕ) (p : b.primeFactors) : ℤ :=
  @legendreSym p.1 ⟨Nat.prime_of_mem_primeFactors p.2⟩
      (Rat.ringOfIntegersEquiv a) ^ b.factorization p.1

open scoped Classical in
private theorem rationalIdealQuadraticSourceFactor_reindexed
    (a : 𝓞 ℚ) (b : ℕ) (hb : b ≠ 0) (hbOdd : Odd b)
    (hab : Nat.Coprime (Rat.ringOfIntegersEquiv a).natAbs b)
    (p : b.primeFactors) :
    rationalIdealQuadraticSourceFactor a b hbOdd hab
        ((rationalPrincipalIdealPrimeDivisorsEquiv b hb).symm p) =
      rationalJacobiPrimeFactor a b p := by
  unfold rationalIdealQuadraticSourceFactor rationalJacobiPrimeFactor
  rw [map_pow]
  rw [idealPrimeMultiplicity_rationalPrincipalIdeal_reindexed b hb p]
  have hpNeTwo : p.1 ≠ 2 := by
    intro hpTwo
    apply hbOdd.not_two_dvd_nat
    simpa only [hpTwo] using Nat.dvd_of_mem_primeFactors p.2
  let P := (rationalPrincipalIdealPrimeDivisorsEquiv b hb).symm p
  have hLegendre :=
    rationalPrimeIdealPowerResidueSymbol_two_eq_legendre
      ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ hpNeTwo a
        (rationalPrincipalIdeal_numerator_not_mem_of_coprime
          a b hab P.1 P.2)
  rw [← hLegendre]
  rfl

open scoped Classical in
/-- The quadratic ideal power-residue symbol of a positive rational
principal ideal is the classical Jacobi symbol.  Oddness supplies the
residue-characteristic condition at every denominator prime, while ordinary
natural coprimality supplies numerator nonvanishing. -/
theorem rationalIdealPowerResidueSymbol_two_eq_jacobiSym
    (a : 𝓞 ℚ) (b : ℕ) (hb : b ≠ 0)
    (hbOdd : Odd b)
    (hab : Nat.Coprime
      (Rat.ringOfIntegersEquiv a).natAbs b) :
    rationalQuadraticRootValue
        (idealPowerResidueSymbol ℚ
          (rationalPrincipalIdeal b)
          (rationalPrincipalIdeal_ne_zero b hb)
          (2 : ℕ+) rationalQuadraticPrimitiveRoots_nonempty_pnat a
          (by
            intro P hP
            change (Ideal.absNorm P.asIdeal).Coprime 2
            exact rationalPrincipalIdeal_absNorm_coprime_two_of_odd
              b hbOdd P hP)
          (rationalPrincipalIdeal_numerator_not_mem_of_coprime a b hab)) =
      jacobiSym (Rat.ringOfIntegersEquiv a) b := by
  let : Fintype
      (idealPrimeDivisors ℚ (rationalPrincipalIdeal b)) :=
    (idealPrimeDivisors_finite ℚ (rationalPrincipalIdeal b)
      (rationalPrincipalIdeal_ne_zero b hb)).fintype
  rw [idealPowerResidueSymbol_eq_prod]
  change rationalQuadraticRootValuePNatMonoidHom _ = _
  rw [map_prod]
  change
    (∏ P : idealPrimeDivisors ℚ (rationalPrincipalIdeal b),
      rationalIdealQuadraticSourceFactor a b hbOdd hab P) = _
  rw [
    prod_rationalPrincipalIdealPrimeDivisors_eq_prod_primeFactors_subtype
      b hb (rationalIdealQuadraticSourceFactor a b hbOdd hab),
    jacobiSym_eq_prod_primeFactors_factorization]
  apply Fintype.prod_congr
  intro p
  exact rationalIdealQuadraticSourceFactor_reindexed
    a b hb hbOdd hab p

end Reciprocity
end GlobalClassFieldTheory
