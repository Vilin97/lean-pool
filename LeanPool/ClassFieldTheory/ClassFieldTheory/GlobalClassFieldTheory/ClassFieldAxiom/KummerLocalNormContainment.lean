/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.CompletionToIdeal
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.LocalNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlace
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.FinitePlaceTensorNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.KummerTheory.Concrete.SimpleExtensionLocalBehavior
/-!
# Local norm containment for Kummer extensions

This module proves that local powers, and then the concrete simple-Kummer
power subgroup, lie in the norm subgroup at a chosen finite place.
-/

open scoped NumberField Classical NNReal IsMulCommutative
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open KummerTheory
open LocalFieldTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/-- Coordinates in `(Z/nZ)^r` show that every Galois automorphism has
exponent dividing `n`. -/
theorem galois_pow_eq_one_of_field_equiv_pi_zmod
    {L : Type*} [Field L] [Algebra K L]
    (n : ℕ+) (r : ℕ)
    (eG :
      (L ≃ₐ[K] L) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ)))) :
    ∀ sigma : L ≃ₐ[K] L, sigma ^ (n : ℕ) = 1 := by
  intro sigma
  apply eG.injective
  rw [map_pow, map_one]
  ext i
  apply Multiplicative.toAdd.injective
  change (n : ℕ) • Multiplicative.toAdd (eG sigma i) = 0
  simp

/-- Local `n`-th powers are norms from the chosen finite-place
completion when every global Galois automorphism has exponent dividing
`n`.  This is the shared local-field core used by the coordinate and
simple-Kummer wrappers below. -/
private theorem
    nthPowerSubgroup_le_chosenFinitePlaceLocalNormSubgroup_of_galois_pow_eq_one
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+)
    (hGlobal :
      ∀ sigma : L ≃ₐ[K] L,
        sigma ^ (n : ℕ) = 1)
    (v : HeightOneSpectrum (𝓞 K)) :
    (powMonoidHom (n : ℕ) :
        (v.adicCompletion K)ˣ →*
          (v.adicCompletion K)ˣ).range ≤
      _root_.chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let w := _root_.chosenFinitePlaceExtension (L := L) v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let :=
    LocalClassFieldTheory.localizedCompletionGlobalAlgebra vK w
  let :=
    LocalClassFieldTheory.localizedCompletionIsScalarTower vK w
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let : FiniteDimensional vK.Completion E :=
    AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite vK hvK w
  let : IsGalois vK.Completion E :=
    HilbertRamification.algebraicLocalization_isGalois vK w
  let : NontriviallyNormedField vK.Completion :=
    absoluteValueExtension_completionNontriviallyNormedField
      vK hvK
  let : LocallyCompactSpace vK.Completion :=
    AbsoluteValue.Completion.locallyCompactSpace
      (_root_.finitePlaceCompletionBaseMap_isometry v)
  let : IsUltrametricDist vK.Completion :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (AbsoluteValue.completionAbsoluteValue_isNonarchimedean
        vK
        (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv
          K v))
  let : Valued vK.Completion ℝ≥0 :=
    NormedField.toValued
  let vC : Valuation vK.Completion ℝ≥0 := Valued.v
  let : vC.IsNontrivial :=
    (inferInstance :
      (NormedField.valuation
        (K := vK.Completion)).IsNontrivial)
  let : ValuativeRel vK.Completion :=
    ValuativeRel.ofValuation vC
  let : vC.Compatible :=
    Valuation.Compatible.ofValuation vC
  let : ValuativeRel.IsNontrivial vK.Completion :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vC).2
      inferInstance
  let : IsValuativeTopology vK.Completion :=
    isValuativeTopology_of_valued_ofValuation
      vK.Completion ℝ≥0
  let : IsNonarchimedeanLocalField vK.Completion :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  let eLocal :
      absoluteValueDecompositionGroup K w.1 ≃*
        (E ≃ₐ[vK.Completion] E) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w
  have hLocal :
      ∀ tau : E ≃ₐ[vK.Completion] E,
        tau ^ (n : ℕ) = 1 := by
    intro tau
    apply eLocal.symm.injective
    rw [map_pow, map_one]
    apply Subtype.ext
    exact hGlobal (eLocal.symm tau).1
  have hAbelianized :
      ∀ a : Abelianization (E ≃ₐ[vK.Completion] E),
        a ^ (n : ℕ) = 1 := by
    intro a
    refine QuotientGroup.induction_on a ?_
    intro tau
    change (Abelianization.of tau) ^ (n : ℕ) = 1
    rw [← map_pow, hLocal tau, map_one]
  intro x hx
  obtain ⟨y, hy⟩ :=
    (MonoidHom.mem_range
      (G := (v.adicCompletion K)ˣ)).mp hx
  rw [powMonoidHom_apply] at hy
  subst x
  let e :
      vK.Completionˣ ≃ₜ* (v.adicCompletion K)ˣ :=
    _root_.finitePlaceCompletionUnitsContinuousMulEquiv v
  change
    y ^ (n : ℕ) ∈
      (localNormSubgroup
        vK.Completion E).map e.toMonoidHom
  refine ⟨(e.symm y) ^ (n : ℕ), ?_, ?_⟩
  · rw [← LocalClassFieldTheory.localArtinMonoidHom_ker]
    change
      LocalClassFieldTheory.localArtinMonoidHom
          vK.Completion E ((e.symm y) ^ (n : ℕ)) = 1
    rw [map_pow]
    exact hAbelianized
      (LocalClassFieldTheory.localArtinMonoidHom
        vK.Completion E (e.symm y))
  · change e ((e.symm y) ^ (n : ℕ)) = y ^ (n : ℕ)
    rw [map_pow, e.apply_symm_apply]

/-- Local `n`-th powers are norms from the chosen finite-place
completion when the global Galois group has exponent dividing `n`. -/
theorem nthPowerSubgroup_le_chosenFinitePlaceLocalNormSubgroup
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+) (r : ℕ)
    (eG :
      (L ≃ₐ[K] L) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (v : HeightOneSpectrum (𝓞 K)) :
    (powMonoidHom (n : ℕ) :
        (v.adicCompletion K)ˣ →*
          (v.adicCompletion K)ˣ).range ≤
      _root_.chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v := by
  exact
    nthPowerSubgroup_le_chosenFinitePlaceLocalNormSubgroup_of_galois_pow_eq_one
      (K := K) (L := L) n
      (galois_pow_eq_one_of_field_equiv_pi_zmod n r eG) v

/-- For the actual simple Kummer extension `K(ⁿ√b)/K`, every local
`n`-th power is a norm at every finite place.  The exponent input is
produced by the concrete Kummer character, rather than supplied as a
hypothesis. -/
theorem chosenSimpleKummerNthPowerSubgroup_le_chosenFinitePlaceLocalNormSubgroup
    {K : Type} [Field K] [NumberField K]
    (n : ℕ+)
    (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (b : Kˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    let E :=
      KummerTheory.chosenSimpleKummerExtension K n hnK b
    letI : FiniteDimensional K E :=
      KummerTheory.chosenSimpleKummerExtension_finiteDimensional
        K n hnK b
    letI : IsAbelianGalois K E :=
      KummerTheory.chosenSimpleKummerExtension_isAbelianGalois
        K n hnK hmu b
    (powMonoidHom (n : ℕ) :
        (v.adicCompletion K)ˣ →*
          (v.adicCompletion K)ˣ).range ≤
      _root_.chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := E) v := by
  let E :=
    KummerTheory.chosenSimpleKummerExtension K n hnK b
  let : FiniteDimensional K E :=
    KummerTheory.chosenSimpleKummerExtension_finiteDimensional
      K n hnK b
  let : IsAbelianGalois K E :=
    KummerTheory.chosenSimpleKummerExtension_isAbelianGalois
      K n hnK hmu b
  exact
    nthPowerSubgroup_le_chosenFinitePlaceLocalNormSubgroup_of_galois_pow_eq_one
      (K := K) (L := E) n
      (KummerTheory.chosenSimpleKummerExtension_galois_pow_eq_one
        K n hnK hmu b) v


end GlobalClassFieldTheory.ClassFieldAxiom
