/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.SimpleExtension
public import LeanPool.ClassFieldTheory.ClassFieldTheory.KummerTheory.Concrete.FinitePlaceDecomposition
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.InfinitePlaces
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.InfinitePlaceTensorBlock
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.CompMulEquiv
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Algebra
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Generator
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.HerbrandEquiv
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Finite
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.H0
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.HMinusOne
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.Trivial
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.Quotient
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlace
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceAction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlock
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockEquiv
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockEquivApply
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockInclusion
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockInducedSmul
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockTensorSmul
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.CompletionTransport
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Spine
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Action
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Equiv
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Inclusion
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.CompletionToIdeal
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.LocalNorm
public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.LocalUnitKummerUnramified
/-!
# Unramified finite places in simple Kummer extensions

This file proves the local unit case of the Kummer ramification criterion.
If both `b` and the exponent `n` are units at a finite place, then the
chosen localization of `K(ⁿ√b) / K` at that place is unramified.

The proof uses the existing algebraic localization, mathlib's minimal
polynomial API, and the complete-DVF different criterion.  No auxiliary
Kummer extension or alternative notion of unramifiedness is introduced.
-/

@[expose] public section

open scoped NumberField NNReal TensorProduct ValuativeRel
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalFieldTheory
open LocalClassFieldTheory

noncomputable section

namespace KummerTheory

variable {K : Type} [Field K] [NumberField K]

open scoped Classical in
private theorem valuativeRelExtension_isNontrivial
    {C F : Type}
    [Field C] [Field F] [Algebra C F]
    [ValuativeRel C] [ValuativeRel F]
    [Valuation.HasExtension
      (ValuativeRel.valuation C) (ValuativeRel.valuation F)]
    [(ValuativeRel.valuation C).IsNontrivial] :
    (ValuativeRel.valuation F).IsNontrivial := {
  exists_val_nontrivial := by
    let vC := ValuativeRel.valuation C
    let vF := ValuativeRel.valuation F
    rcases Valuation.IsNontrivial.exists_val_nontrivial
        (v := vC) with ⟨x, hx0, hx1⟩
    refine ⟨algebraMap C F x, ?_, ?_⟩
    · intro h
      have hm :
          vF (algebraMap C F x) =
            vF (algebraMap C F 0) := by
        simpa only [map_zero] using h
      exact hx0 (by
        simpa only [map_zero] using
          ((Valuation.HasExtension.val_map_eq_iff vC vF x 0).1 hm))
    · intro h
      have hm :
          vF (algebraMap C F x) =
            vF (algebraMap C F 1) := by
        simpa only [map_one] using h
      exact hx1 (by
        simpa only [map_one] using
          ((Valuation.HasExtension.val_map_eq_iff vC vF x 1).1 hm)) }

open scoped Classical in
/-- A finite Galois number-field extension generated by an `n`-th root of a
unit is unramified at every chosen completion where both the radicand and
`n` are units.

This is the source-producing Kummer criterion: the proof works on the
actual localized completion, proves that the chosen root generates it,
and applies the derivative/different criterion to `X ^ n - b`. -/
theorem
    kummerGeneratedExtension_chosenFinitePlaceIsUnramified_of_valuation_eq_one
    {L : Type}
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+)
    (b : Kˣ)
    (beta : Lˣ)
    (hbeta :
      beta ^ (n : ℕ) =
        Units.map (algebraMap K L).toMonoidHom b)
    (hgen :
      IntermediateField.adjoin K
        ({(beta : L)} : Set L) = ⊤)
    (v : HeightOneSpectrum (𝓞 K))
    (hb : v.valuation K (b : K) = 1)
    (hn : v.valuation K ((n : ℕ) : K) = 1) :
    ChosenFinitePlaceIsUnramified
      (K := K) (L := L) v := by
  let vK := HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    HeightOneSpectrum.isNonarchimedean_adicAbv K v
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let := localizedCompletionGlobalAlgebra vK w
  let := localizedCompletionIsScalarTower vK w
  let C := vK.Completion
  let F := LocalizedCompletion vK w
  let : FiniteDimensional C F :=
    localizedCompletionModuleFinite vK hvK w
  let : IsGalois C F :=
    HilbertRamification.algebraicLocalization_isGalois vK w
  let : NontriviallyNormedField C :=
    absoluteValueExtensionCompletionNontriviallyNormedField vK hvK
  let : LocallyCompactSpace C :=
    AbsoluteValue.Completion.locallyCompactSpace
      (finitePlaceCompletionBaseMap_isometry v)
  let : IsUltrametricDist C :=
    completionIsUltrametricDist vK hvKna
  let : Valued C ℝ≥0 :=
    finitePlaceCompletionValued vK hvKna
  let vCNorm : Valuation C ℝ≥0 := Valued.v
  let : vCNorm.IsNontrivial :=
    (inferInstance :
      (NormedField.valuation (K := C)).IsNontrivial)
  let : ValuativeRel C :=
    finitePlaceCompletionValuativeRel vK hvKna
  let : vCNorm.Compatible :=
    Valuation.Compatible.ofValuation vCNorm
  let : ValuativeRel.IsNontrivial C :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vCNorm).2
      inferInstance
  let vC := ValuativeRel.valuation C
  let : vC.IsNontrivial := inferInstance
  let : IsValuativeTopology C :=
    isValuativeTopology_of_valued_ofValuation C ℝ≥0
  let : IsNonarchimedeanLocalField C :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  let : FiniteDimensional C w.1.Completion :=
    completionModuleFinite vK hvK w
  let : ContinuousSMul C w.1.Completion :=
    continuousSMul_of_algebraMap _ _
      (AbsoluteValue.completionMap_isometry vK w.1 w.2).continuous
  let : LocallyCompactSpace w.1.Completion :=
    LocallyCompactSpace.of_finiteDimensional_of_complete
      C w.1.Completion
  let eCompletion : F ≃ᵢ w.1.Completion :=
    { toEquiv :=
        (localizedCompletionEquivCompletion
          vK hvK w).toEquiv
      isometry_toFun := Isometry.of_dist_eq fun _ _ => rfl }
  let : LocallyCompactSpace F :=
    (eCompletion.toHomeomorph.locallyCompactSpace_iff).2
      inferInstance
  let : IsUltrametricDist F :=
    localizedCompletionIsUltrametricDist
      vK w hvKna
  let : Valued F ℝ≥0 :=
    localizedCompletionFinitePlaceValued
      vK w hvKna
  let : ValuativeRel F :=
    localizedCompletionFinitePlaceValuativeRel
      vK w hvKna
  let vFNorm : Valuation F ℝ≥0 := Valued.v
  let : vFNorm.Compatible :=
    Valuation.Compatible.ofValuation vFNorm
  let vF := ValuativeRel.valuation F
  let : Valuation.HasExtension vC vF :=
    localizedCompletionValuationHasExtension
      vK w hvKna
  let : vF.IsNontrivial :=
    valuativeRelExtension_isNontrivial (C := C) (F := F)
  let : ValuativeRel.IsNontrivial F :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vF).2
      inferInstance
  let : IsValuativeTopology F :=
    isValuativeTopology_of_valued_ofValuation F ℝ≥0
  let : IsNonarchimedeanLocalField F :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  let : Algebra 𝒪[C] F :=
    Algebra.ofSubsemiring 𝒪[C]
  let :=
    localizedCompletionIsIntegralClosureWithExtension
      vK w hvK hvKna
  let : Module.Finite 𝒪[C] 𝒪[F] :=
    integerRing_moduleFinite_of_isIntegralClosure C F
  have hbAbv : vK (b : K) = 1 := by
    rw [HeightOneSpectrum.adicAbv_def, hb]
    simp
  have hnAbv : vK ((n : ℕ) : K) = 1 := by
    rw [HeightOneSpectrum.adicAbv_def, hn]
    simp
  have hbNorm :
      ‖algebraMap K C (b : K)‖ = 1 := by
    calc
      ‖algebraMap K C (b : K)‖ = vK (b : K) :=
        AbsoluteValue.completionAbsoluteValue_coe vK (b : K)
      _ = 1 := hbAbv
  let bC : C := algebraMap K C (b : K)
  have hbCNorm : vCNorm bC = 1 := by
    change ‖bC‖₊ = 1
    exact NNReal.eq (by simpa [bC] using hbNorm)
  have hbCVal : vC bC = 1 :=
    (ValuativeRel.isEquiv vCNorm vC).eq_one_iff_eq_one.mp hbCNorm
  have hnNorm : ‖((n : ℕ) : C)‖ = 1 := by
    calc
      ‖((n : ℕ) : C)‖ =
          ‖algebraMap K C ((n : ℕ) : K)‖ := by
            rw [map_natCast]
      _ = vK ((n : ℕ) : K) :=
        AbsoluteValue.completionAbsoluteValue_coe vK ((n : ℕ) : K)
      _ = 1 := hnAbv
  let nC : C := (n : ℕ)
  have hnCNorm : vCNorm nC = 1 := by
    change ‖nC‖₊ = 1
    exact NNReal.eq (by simpa [nC] using hnNorm)
  have hnCVal : vC nC = 1 :=
    (ValuativeRel.isEquiv vCNorm vC).eq_one_iff_eq_one.mp hnCNorm
  let betaL : L := (beta : L)
  let betaF : F :=
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 betaL
  have hbetaLpow :
      betaL ^ (n : ℕ) = algebraMap K L (b : K) :=
    congrArg Units.val hbeta
  have hbetaFpow :
      betaF ^ (n : ℕ) =
        algebraMap C F (algebraMap K C (b : K)) := by
    have hmap :=
      congrArg
        (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2)
        hbetaLpow
    simpa only [betaF, map_pow,
      AbsoluteValue.toAlgebraicLocalization_algebraMap] using hmap
  have hbetaWpow : (w.1 betaL) ^ (n : ℕ) = 1 := by
    calc
      (w.1 betaL) ^ (n : ℕ) = w.1 (betaL ^ (n : ℕ)) := by
        rw [map_pow]
      _ = w.1 (algebraMap K L (b : K)) := by rw [hbetaLpow]
      _ = vK (b : K) := w.2 (b : K)
      _ = 1 := hbAbv
  have hbetaW : w.1 betaL = 1 :=
    (pow_eq_one_iff_of_nonneg (w.1.nonneg betaL) n.ne_zero).mp
      hbetaWpow
  have hbetaNorm : ‖betaF‖ = 1 := by
    change
      AbsoluteValue.algebraicLocalizationAbsoluteValue
          vK w.1 w.2 betaF = 1
    rw [
      AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization,
      hbetaW]
  have hbetaFNorm : vFNorm betaF = 1 := by
    change ‖betaF‖₊ = 1
    exact NNReal.eq hbetaNorm
  have hbetaFVal : vF betaF = 1 :=
    (ValuativeRel.isEquiv vFNorm vF).eq_one_iff_eq_one.mp hbetaFNorm
  have hglobal : IntermediateField.adjoin K {betaL} = ⊤ := by
    simpa only [betaL] using hgen
  have hR : IntermediateField.adjoin C {betaF} = ⊤ := by
    simpa only [C, F, betaF] using
      localizedCompletion_adjoin_image_eq_top_of_adjoin_eq_top
        vK w betaL hglobal
  have hgenF : Algebra.adjoin C {betaF} = ⊤ := by
    apply
      (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic betaF)).mp
    exact hR
  change IsNonarchimedeanLocalField.IsUnramifiedValuedExtension C F
  exact
    isUnramifiedValuedExtension_of_unit_kummer_generator
      n bC betaF hbCVal hnCVal hbetaFVal hbetaFpow hgenF

open scoped Classical in
/-- A chosen simple Kummer extension is unramified at a finite place where its
radicand and exponent are units.  This is the direct specialization of
the generated-extension derivative criterion above. -/
theorem
    chosenSimpleKummerExtension_chosenFinitePlaceIsUnramified_of_valuation_eq_one
    (n : ℕ+)
    (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (b : Kˣ)
    (v : HeightOneSpectrum (𝓞 K))
    (hb : v.valuation K (b : K) = 1)
    (hn : v.valuation K ((n : ℕ) : K) = 1) :
    let L := chosenSimpleKummerExtension K n hnK b
    letI : FiniteDimensional K L :=
      chosenSimpleKummerExtension_finiteDimensional K n hnK b
    letI : IsAbelianGalois K L :=
      chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
    letI : NumberField L :=
      NumberField.of_module_finite K L
    ChosenFinitePlaceIsUnramified
      (K := K) (L := L) v := by
  let L := chosenSimpleKummerExtension K n hnK b
  let : FiniteDimensional K L :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let : IsAbelianGalois K L :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let : NumberField L :=
    NumberField.of_module_finite K L
  let beta : Lˣ :=
    chosenSimpleKummerRootUnit K n hnK b
  apply
    kummerGeneratedExtension_chosenFinitePlaceIsUnramified_of_valuation_eq_one
      (K := K) (L := L) n b beta
  · dsimp only [L, beta]
    exact chosenSimpleKummerRootUnit_pow K n hnK b
  · simpa [L, beta] using
      chosenSimpleKummerExtension_adjoin_root_eq_top K n hnK b
  · exact hb
  · exact hn

open scoped Classical in
/-- At every finite place above a base place where the radicand and exponent
are units, the chosen simple Kummer extension is globally unramified in the
ideal-theoretic sense. -/
theorem
    chosenSimpleKummerExtension_isUnramifiedAt_at_all_finitePlacesAbove_of_valuation_eq_one
    (n : ℕ+)
    (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (b : Kˣ)
    (v : HeightOneSpectrum (𝓞 K))
    (hb : v.valuation K (b : K) = 1)
    (hn : v.valuation K ((n : ℕ) : K) = 1) :
    let L := chosenSimpleKummerExtension K n hnK b
    letI : FiniteDimensional K L :=
      chosenSimpleKummerExtension_finiteDimensional K n hnK b
    letI : IsAbelianGalois K L :=
      chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
    letI : NumberField L :=
      NumberField.of_module_finite K L
    ∀ P : HeightOneSpectrum (𝓞 L),
      finitePlaceBelow (K := K) P = v →
        Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal := by
  let L := chosenSimpleKummerExtension K n hnK b
  let _ : FiniteDimensional K L :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let _ : IsAbelianGalois K L :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let _ : NumberField L :=
    NumberField.of_module_finite K L
  have hunram :
      ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v := by
    simpa only [L] using
      chosenSimpleKummerExtension_chosenFinitePlaceIsUnramified_of_valuation_eq_one
        (K := K) n hnK hmu b v hb hn
  change ∀ P : HeightOneSpectrum (𝓞 L),
    finitePlaceBelow (K := K) P = v →
      Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal
  intro P hP
  exact
    isUnramifiedAt_at_finitePlaceAbove_of_chosenFinitePlaceIsUnramified
      (K := K) (L := L) (v := v) (P := P)
      (hP := hP) (hunram := hunram)

open scoped Classical in
/-- A finite place splits completely in the chosen simple Kummer extension when
the radicand is already an `n`-th power in the completion.  This is the
finite-place splitting source used in the local splitting analysis of simple radical extensions. -/
theorem
    chosenSimpleKummerExtension_finitePlaceSplitsCompletely_of_mem_nthPowerSubgroup
    (n : ℕ+)
    (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (b : Kˣ)
    (v : HeightOneSpectrum (𝓞 K))
    (hb :
      Units.map
            (algebraMap K (v.adicCompletion K)).toMonoidHom b ∈
        (powMonoidHom (n : ℕ) :
          (v.adicCompletion K)ˣ →*
            (v.adicCompletion K)ˣ).range) :
    let E := chosenSimpleKummerExtension K n hnK b
    letI : FiniteDimensional K E :=
      chosenSimpleKummerExtension_finiteDimensional K n hnK b
    letI : IsAbelianGalois K E :=
      chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
    FinitePlaceSplitsCompletely
      (K := K) (L := E) v := by
  let E := chosenSimpleKummerExtension K n hnK b
  let : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let beta : Eˣ :=
    chosenSimpleKummerRootUnit K n hnK b
  have hbeta :
      beta ^ (n : ℕ) =
        Units.map (algebraMap K E).toMonoidHom b := by
    dsimp only [E, beta]
    exact chosenSimpleKummerRootUnit_pow K n hnK b
  let D : Subgroup (E ≃ₐ[K] E) :=
    absoluteValueDecompositionGroup K
      (chosenFinitePlaceExtension (L := E) v).1
  have hfixed :
      (beta : E) ∈
        IntermediateField.fixedField D := by
    simpa only [D] using
      (finitePlaceKummerRadicand_mem_nthPowerSubgroup_iff_root_mem_decompositionFixedField
        (K := K) (L := E) v n hmu b beta hbeta).mp hb
  have hgen :
      IntermediateField.adjoin K ({(beta : E)} : Set E) = ⊤ := by
    simpa [E, beta] using
      chosenSimpleKummerExtension_adjoin_root_eq_top K n hnK b
  have hle :
      IntermediateField.adjoin K ({(beta : E)} : Set E) ≤
        IntermediateField.fixedField D := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    have hx' : x = (beta : E) :=
      Set.mem_singleton_iff.mp hx
    subst x
    exact hfixed
  have htop :
      IntermediateField.fixedField D = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact hle
  change D = ⊥
  rw [← IntermediateField.fixingSubgroup_fixedField D,
    htop, IntermediateField.fixingSubgroup_top]

omit [NumberField K] in
open scoped Classical in
/-- The local Kummer root forces the infinite decomposition group to be trivial. -/
private theorem
    chosenSimpleKummerExtension_infiniteDecompositionGroup_eq_bot_of_mem_nthPowerSubgroup
    (n : ℕ+)
    (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (b : Kˣ)
    (w : InfinitePlace K)
    (hb :
      Units.map
            (algebraMap K w.Completion).toMonoidHom b ∈
        (powMonoidHom (n : ℕ) :
          w.Completionˣ →* w.Completionˣ).range) :
    let E := chosenSimpleKummerExtension K n hnK b
    letI : FiniteDimensional K E :=
      chosenSimpleKummerExtension_finiteDimensional K n hnK b
    letI : IsAbelianGalois K E :=
      chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
    let vK : AbsoluteValue K ℝ := w.1
    let u : AbsoluteValueExtension vK E :=
      pullbackAbsoluteValueExtension vK w.isNontrivial IsAlgClosed.lift
    absoluteValueDecompositionGroup K u.1 = ⊥ := by
  let E := chosenSimpleKummerExtension K n hnK b
  let : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let vK : AbsoluteValue K ℝ := w.1
  let hvK : vK.IsNontrivial := w.isNontrivial
  let u : AbsoluteValueExtension vK E :=
    pullbackAbsoluteValueExtension
      vK hvK IsAlgClosed.lift
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) u.1
  let : SMul K u.1.Completion := hK.toSMul
  let : Algebra vK.Completion u.1.Completion :=
    AbsoluteValue.completionAlgebra vK u.1 u.2
  let := localizedCompletionGlobalAlgebra vK u
  let := localizedCompletionIsScalarTower vK u
  let C := vK.Completion
  let F := LocalizedCompletion vK u
  let eK : w.Completion ≃+* C :=
    (infinitePlaceCompletionAlgEquiv
      (K := K) w).toRingEquiv
  let eC : w.Completionˣ ≃* Cˣ :=
    Units.mapEquiv eK.toMulEquiv
  let : FiniteDimensional C F :=
    localizedCompletionModuleFinite vK hvK u
  let : IsGalois C F :=
    HilbertRamification.algebraicLocalization_isGalois vK u
  let beta : Eˣ :=
    chosenSimpleKummerRootUnit K n hnK b
  have hbeta :
      beta ^ (n : ℕ) =
        Units.map (algebraMap K E).toMonoidHom b := by
    dsimp only [E, beta]
    exact chosenSimpleKummerRootUnit_pow K n hnK b
  have hbC :
      Units.map
            (algebraMap K C).toMonoidHom b ∈
        (powMonoidHom (n : ℕ) : Cˣ →* Cˣ).range := by
    obtain ⟨y, hy⟩ :=
      (MonoidHom.mem_range
        (G := w.Completionˣ)).mp hb
    refine
      (MonoidHom.mem_range
        (G := Cˣ)).mpr ⟨eC y, ?_⟩
    rw [powMonoidHom_apply] at hy ⊢
    calc
      (eC y) ^ (n : ℕ) =
          eC (y ^ (n : ℕ)) :=
        (map_pow eC y (n : ℕ)).symm
      _ =
          eC
            (Units.map
              (algebraMap K w.Completion).toMonoidHom b) :=
        congrArg eC hy
      _ =
          Units.map
            (algebraMap K C).toMonoidHom b := by
        apply Units.ext
        simpa [eC, eK, C, vK] using
          (infinitePlaceCompletionAlgEquiv
            (K := K) w).commutes (b : K)
  have hfixed :
      (beta : E) ∈
        IntermediateField.fixedField
          (absoluteValueDecompositionGroup K u.1) := by
    apply
      kummerRadicand_root_mem_decompositionFixedField_of_mem_nthPowerSubgroup
        (K := K) (L := E) vK hvK u n hmu b beta hbeta
    exact hbC
  let D : Subgroup (E ≃ₐ[K] E) :=
    absoluteValueDecompositionGroup K u.1
  have hgen :
      IntermediateField.adjoin K ({(beta : E)} : Set E) = ⊤ := by
    simpa [E, beta] using
      chosenSimpleKummerExtension_adjoin_root_eq_top K n hnK b
  have hle :
      IntermediateField.adjoin K ({(beta : E)} : Set E) ≤
        IntermediateField.fixedField D := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    have hx' : x = (beta : E) :=
      Set.mem_singleton_iff.mp hx
    subst x
    change
      (beta : E) ∈
        IntermediateField.fixedField
          (absoluteValueDecompositionGroup K u.1)
    exact hfixed
  have htop :
      IntermediateField.fixedField D = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact hle
  have hD : D = ⊥ := by
    rw [← IntermediateField.fixingSubgroup_fixedField D,
      htop, IntermediateField.fixingSubgroup_top]
  exact hD

omit [NumberField K] in
open scoped Classical in
/-- At an infinite place where the radicand is already an `n`-th
power, the determinant norm from the simple Kummer tensor algebra is
surjective.  The proof identifies the decomposition group with the
trivial group and then uses the canonical local tensor norm theorem. -/
theorem
    chosenSimpleKummerExtension_infiniteTensorNormSubgroup_eq_top_of_mem_nthPowerSubgroup
    (n : ℕ+)
    (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (b : Kˣ)
    (w : InfinitePlace K)
    (hb :
      Units.map
            (algebraMap K w.Completion).toMonoidHom b ∈
        (powMonoidHom (n : ℕ) :
          w.Completionˣ →* w.Completionˣ).range) :
    let E := chosenSimpleKummerExtension K n hnK b
    letI : FiniteDimensional K E :=
      chosenSimpleKummerExtension_finiteDimensional K n hnK b
    letI : IsAbelianGalois K E :=
      chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
    infiniteTensorNormSubgroup
      (K := K) (L := E) w = ⊤ := by
  let E := chosenSimpleKummerExtension K n hnK b
  let : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let vK : AbsoluteValue K ℝ := w.1
  let hvK : vK.IsNontrivial := w.isNontrivial
  let u : AbsoluteValueExtension vK E :=
    pullbackAbsoluteValueExtension
      vK hvK IsAlgClosed.lift
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) u.1
  let : SMul K u.1.Completion := hK.toSMul
  let : Algebra vK.Completion u.1.Completion :=
    AbsoluteValue.completionAlgebra vK u.1 u.2
  let := localizedCompletionGlobalAlgebra vK u
  let := localizedCompletionIsScalarTower vK u
  let C := vK.Completion
  let F := LocalizedCompletion vK u
  let eK : w.Completion ≃+* C :=
    (infinitePlaceCompletionAlgEquiv
      (K := K) w).toRingEquiv
  let eC : w.Completionˣ ≃* Cˣ :=
    Units.mapEquiv eK.toMulEquiv
  let : FiniteDimensional C F :=
    localizedCompletionModuleFinite vK hvK u
  let : IsGalois C F :=
    HilbertRamification.algebraicLocalization_isGalois vK u
  let D : Subgroup (E ≃ₐ[K] E) :=
    absoluteValueDecompositionGroup K u.1
  have hD : D = ⊥ :=
    chosenSimpleKummerExtension_infiniteDecompositionGroup_eq_bot_of_mem_nthPowerSubgroup
      n hnK hmu b w hb
  let eLocal :
      D ≃* (F ≃ₐ[C] F) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK u
  have hdegree :
      Module.finrank C F = 1 := by
    calc
      Module.finrank C F =
          Nat.card (F ≃ₐ[C] F) :=
        (IsGalois.card_aut_eq_finrank C F).symm
      _ = Nat.card D :=
        (Nat.card_congr eLocal.toEquiv).symm
      _ = 1 := by
        rw [hD]
        simp
  let : Module.Free C F :=
    Module.Free.of_divisionRing C F
  have hNormTop :
      localNormSubgroup C F = ⊤ := by
    apply top_unique
    intro x _
    refine
      ⟨Units.map (algebraMap C F).toMonoidHom x, ?_⟩
    apply Units.ext
    change
      Algebra.norm C (algebraMap C F (x : C)) =
        (x : C)
    rw [Algebra.norm_algebraMap, hdegree, pow_one]
  have hLocalTensorTop :
      localTensorNormSubgroup
          (K := K) (L := E) vK =
        ⊤ := by
    rw [localTensorNormSubgroup_eq_localNormSubgroup
      (K := K) (L := E) vK u hvK]
    exact hNormTop
  let eA :
      (w.Completion ⊗[K] E) ≃+*
        LocalTensorAlgebra (L := E) vK :=
    (infinitePlaceLocalTensorAlgEquiv
      (K := K) (L := E) w).toRingEquiv
  let eU :
      (w.Completion ⊗[K] E)ˣ ≃*
        (LocalTensorAlgebra (L := E) vK)ˣ :=
    infinitePlaceLocalTensorUnitsEquiv
      (K := K) (L := E) w
  have hnorm
      (z : (w.Completion ⊗[K] E)ˣ) :
      eC
          (infiniteTensorDetNorm
            (K := K) (L := E) w z) =
        localTensorDetNorm
          (K := K) (L := E) vK (eU z) := by
    apply Units.ext
    change
      eK
          (Algebra.norm w.Completion
            (z : w.Completion ⊗[K] E)) =
        Algebra.norm C
          (eA (z : w.Completion ⊗[K] E))
    exact
      _root_.map_norm_tensorProduct_baseChange
        (K := K) (L := E)
        (infinitePlaceCompletionAlgEquiv
          (K := K) w).toAlgHom
        (z : w.Completion ⊗[K] E)
  apply top_unique
  intro x _
  have hx :
      eC x ∈
        localTensorNormSubgroup
          (K := K) (L := E) vK := by
    rw [hLocalTensorTop]
    trivial
  obtain ⟨z, hz⟩ := hx
  refine ⟨eU.symm z, ?_⟩
  apply eC.injective
  rw [hnorm, eU.apply_symm_apply, hz]

end KummerTheory
