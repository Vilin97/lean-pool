/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardUnramified
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedFrobeniusEvaluation
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormalizedIntegerValuation
/-!
# Residue embedding for the completed standard/changed compositum

The finite standard/changed compositum is realized inside the completed
Lubin--Tate level.  Uniqueness of the finite extension of the p-adic
valuation therefore gives a canonical injection from its residue field into
the residue field of the ambient completed level.

This injection is the faithful comparison map used to identify the finite
relative Artin candidate with inverse arithmetic Frobenius.
-/

@[expose] public section

noncomputable
section

namespace LubinTate

open scoped ValuativeRel

open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

/-- The actual finite changed-uniformizer Lubin--Tate level is totally
ramified, hence its residue field is still `𝔽_p`. -/
theorem padicChangedUniformizerLevelResidueField_card
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    let hπ :=
      standardLubinTateChangedUniformizer_isUniformizer
        (padicMultiplicativeLubinTateSeries_isUniformizer p) u
    Nat.card
        (standardLubinTateLevelCompleteDVF hπ n).residueField =
      p := by
  let F := padicLocalField p
  have h₀ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let hπ :=
    standardLubinTateChangedUniformizer_isUniformizer
      h₀ u
  let base := F.toCompleteDVF
  let target := standardLubinTateLevelCompleteDVF hπ n
  let d := degree base.toDVF target.toDVF
  let f := residueDegree base.toDVF target.toDVF
  have hbaseCard : Nat.card base.residueField = p := by
    change Nat.card (padicCompleteDVF p).residueField = p
    exact padicCompleteDVF_residueField_card p
  have hd : 0 < d := by
    rw [show d =
        Module.finrank ℚ_[p]
          (standardLubinTateLevelField hπ n) by
      rfl,
      standardLubinTateLevelField_finrank hπ n,
      hbaseCard]
    exact Nat.mul_pos
      (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
      (Nat.pow_pos (Fact.out : p.Prime).pos)
  have hf : f = 1 := by
    have hfund :=
      standardLubinTateLevelCompleteDVF_fundamentalIdentity hπ n
    rw [standardLubinTateLevel_ramificationIndex_eq_degree hπ n]
      at hfund
    apply Nat.eq_of_mul_eq_mul_left hd
    simpa only [mul_one, d, f] using hfund.symm
  let : FiniteDimensional base.residueField target.residueField :=
    residueField_finiteDimensional_of_moduleFinite base target
  have hfinrank :
      f = Module.finrank base.residueField target.residueField := by
    exact residueDegree_eq_finrank_quotient base target
  calc
    Nat.card target.residueField =
        Nat.card base.residueField ^
          Module.finrank base.residueField target.residueField :=
      Module.natCard_eq_pow_finrank
    _ = Nat.card base.residueField ^ f := by
      rw [← hfinrank]
    _ = p := by rw [hf, pow_one, hbaseCard]

/-- The completed changed-uniformizer fixed field has residue field
cardinality `p`.  The proof transports the residue field in both directions
along the genuine equivalence with the finite changed Lubin--Tate level and
uses uniqueness of finite extensions of the p-adic valuation. -/
theorem padicCompletedChangedUniformizerFixedField_residueField_card
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    let D := padicCompletedChangedUniformizerFixedField p u n
    letI : NontriviallyNormedField D :=
      finiteExtensionSpectralNormedField ℚ_[p] D
    letI : ValuativeRel D :=
      finiteExtensionSpectralValuativeRel ℚ_[p] D
    letI : IsNonarchimedeanLocalField D :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
    Nat.card (localCompleteDVF D).residueField = p := by
  let F := padicLocalField p
  let hπ :=
    standardLubinTateChangedUniformizer_isUniformizer
      (padicMultiplicativeLubinTateSeries_isUniformizer p) u
  let L := standardLubinTateLevelField hπ n
  let D := padicCompletedChangedUniformizerFixedField p u n
  let padicBase := F.toCompleteDVF
  let targetL := standardLubinTateLevelCompleteDVF hπ n
  let e : L ≃ₐ[ℚ_[p]] D :=
    padicChangedUniformizerLevelEquivCompletedFixedField p u n
  let : FiniteDimensional ℚ_[p] L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois ℚ_[p] L :=
    standardLubinTateLevelField_isAbelianGalois F hπ n
  let : NontriviallyNormedField D :=
    finiteExtensionSpectralNormedField ℚ_[p] D
  let : ValuativeRel D :=
    finiteExtensionSpectralValuativeRel ℚ_[p] D
  let : IsNonarchimedeanLocalField D :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
  let targetD := localCompleteDVF D
  let :
      Valuation.HasExtension (ValuativeRel.valuation ℚ_[p])
        (ValuativeRel.valuation D) :=
    finiteExtensionSpectralValuation_hasExtension ℚ_[p] D
  let :
      (localCompleteDVF ℚ_[p]).valuation.HasExtension
        targetD.valuation :=
    localCompleteDVFValuation_hasExtension ℚ_[p] D
  let : padicBase.valuation.HasExtension targetD.valuation :=
    padicLocalFieldValuation_hasExtension_of_localCompleteDVF
      p targetD.valuation
  let inclusionLD : L →+* D := e.toRingHom
  have inclusionLD_comp :
      inclusionLD.comp (algebraMap ℚ_[p] L) =
        algebraMap ℚ_[p] D := by
    apply RingHom.ext
    intro x
    exact e.commutes x
  let :
      padicBase.valuation.HasExtension
        (targetD.valuation.comap inclusionLD) :=
    hasExtension_comap_of_algebraMap_compatible
      inclusionLD inclusionLD_comp
  have hEquivLD :
      targetL.valuation.IsEquiv
        (targetD.valuation.comap inclusionLD) :=
    valuation_isEquiv_of_finite_separable
      padicBase targetL (targetD.valuation.comap inclusionLD)
  let residueLD : targetL.residueField →+* targetD.residueField :=
    residueFieldMapOfIsEquivComap
      targetL.valuation targetD.valuation inclusionLD hEquivLD
  let inclusionDL : D →+* L := e.symm.toRingHom
  have inclusionDL_comp :
      inclusionDL.comp (algebraMap ℚ_[p] D) =
        algebraMap ℚ_[p] L := by
    apply RingHom.ext
    intro x
    exact e.symm.commutes x
  let :
      padicBase.valuation.HasExtension
        (targetL.valuation.comap inclusionDL) :=
    hasExtension_comap_of_algebraMap_compatible
      inclusionDL inclusionDL_comp
  have hEquivDL :
      targetD.valuation.IsEquiv
        (targetL.valuation.comap inclusionDL) :=
    valuation_isEquiv_of_finite_separable
      padicBase targetD (targetL.valuation.comap inclusionDL)
  let residueDL : targetD.residueField →+* targetL.residueField :=
    residueFieldMapOfIsEquivComap
      targetD.valuation targetL.valuation inclusionDL hEquivDL
  let : FiniteDimensional padicBase.residueField targetL.residueField :=
    residueField_finiteDimensional_of_moduleFinite
      padicBase targetL
  let : Finite padicBase.residueField := by
    change Finite (padicCompleteDVF p).residueField
    exact padicCompleteDVF_residueField_finite p
  let : Finite targetL.residueField :=
    Module.finite_of_finite padicBase.residueField
  let : Finite targetD.residueField := by
    change Finite 𝓀[D]
    infer_instance
  have hLD :
      Nat.card targetL.residueField ≤ Nat.card targetD.residueField :=
    Nat.card_le_card_of_injective residueLD residueLD.injective
  have hDL :
      Nat.card targetD.residueField ≤ Nat.card targetL.residueField :=
    Nat.card_le_card_of_injective residueDL residueDL.injective
  calc
    Nat.card targetD.residueField =
        Nat.card targetL.residueField :=
      le_antisymm hDL hLD
    _ = p :=
      padicChangedUniformizerLevelResidueField_card p u n

/-- Relative residue arithmetic Frobenius for the finite
standard/changed compositum is the `p`-power map. -/
theorem
    padicCompletedStandardChangedCompositum_residueArithmeticFrobenius_apply
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    let D := padicCompletedChangedUniformizerFixedField p u n
    let M := padicCompletedStandardChangedCompositum p u n
    letI : NontriviallyNormedField D :=
      finiteExtensionSpectralNormedField ℚ_[p] D
    letI : ValuativeRel D :=
      finiteExtensionSpectralValuativeRel ℚ_[p] D
    letI : IsNonarchimedeanLocalField D :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
    letI : NontriviallyNormedField M :=
      finiteExtensionSpectralNormedField ℚ_[p] M
    letI : ValuativeRel M :=
      finiteExtensionSpectralValuativeRel ℚ_[p] M
    let : IsNonarchimedeanLocalField M :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
    let :
        Valuation.HasExtension (ValuativeRel.valuation D)
          (ValuativeRel.valuation M) :=
      finiteExtensionSpectralValuation_hasExtension_of_tower
        ℚ_[p] D M
    ∀ x : IsLocalRing.ResidueField
        (localCompleteDVF M).valuation.valuationSubring,
      residueExtensionArithmeticFrobeniusOfValuationExtension
          D M x =
        x ^ p := by
  dsimp only
  let D := padicCompletedChangedUniformizerFixedField p u n
  let M := padicCompletedStandardChangedCompositum p u n
  let : NontriviallyNormedField D :=
    finiteExtensionSpectralNormedField ℚ_[p] D
  let : ValuativeRel D :=
    finiteExtensionSpectralValuativeRel ℚ_[p] D
  let : IsNonarchimedeanLocalField D :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
  let : NontriviallyNormedField M :=
    finiteExtensionSpectralNormedField ℚ_[p] M
  let : ValuativeRel M :=
    finiteExtensionSpectralValuativeRel ℚ_[p] M
  let : IsNonarchimedeanLocalField M :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
  let :
      Valuation.HasExtension (ValuativeRel.valuation D)
        (ValuativeRel.valuation M) :=
    finiteExtensionSpectralValuation_hasExtension_of_tower
      ℚ_[p] D M
  have hM :
      IsLocalRing.ResidueField
          (localCompleteDVF M).valuation.valuationSubring =
        𝓀[M] := by
    rw [localCompleteDVF_valuation_eq M]
    rfl
  have hD :
      IsLocalRing.ResidueField
          (localCompleteDVF D).valuation.valuationSubring =
        𝓀[D] := by
    rw [localCompleteDVF_valuation_eq D]
    rfl
  have hcard :=
    padicCompletedChangedUniformizerFixedField_residueField_card p u n
  dsimp only at hcard
  have hcardRaw : Nat.card 𝓀[D] = p := by
    rw [← hD]
    exact hcard
  cases hM
  cases hD
  intro x
  exact
    (residueExtensionArithmeticFrobeniusOfValuationExtension_apply D M
      (show 𝓀[M] from x)).trans
      (congrArg (fun k : ℕ => (show 𝓀[M] from x) ^ k) hcardRaw)

/-- The residue field of the completed changed-uniformizer fixed field embeds
into the residue field of the ambient completed Lubin--Tate level. -/
noncomputable def padicCompletedChangedFieldResidueEmbedding
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    let D := padicCompletedChangedUniformizerFixedField p u n
    letI : NontriviallyNormedField D :=
      finiteExtensionSpectralNormedField ℚ_[p] D
    letI : ValuativeRel D :=
      finiteExtensionSpectralValuativeRel ℚ_[p] D
    letI : IsNonarchimedeanLocalField D :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
    IsLocalRing.ResidueField
        (localCompleteDVF D).valuationSubring →+*
      IsLocalRing.ResidueField
        (padicCompletedLevelCompleteDVF p n).valuationSubring := by
  let D := padicCompletedChangedUniformizerFixedField p u n
  let E := padicCompletedLevelField p n
  let padicBase := (padicLocalField p).toCompleteDVF
  let canonicalBase := localCompleteDVF ℚ_[p]
  let coefficient := padicCompletedUnramifiedCompleteDVF p
  let ambient := padicCompletedLevelCompleteDVF p n
  letI : NontriviallyNormedField D :=
    finiteExtensionSpectralNormedField ℚ_[p] D
  letI : ValuativeRel D :=
    finiteExtensionSpectralValuativeRel ℚ_[p] D
  let : IsNonarchimedeanLocalField D :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
  let :
      Valuation.HasExtension (ValuativeRel.valuation ℚ_[p])
        (ValuativeRel.valuation D) :=
    finiteExtensionSpectralValuation_hasExtension ℚ_[p] D
  let :
      canonicalBase.valuation.HasExtension
        (localCompleteDVF D).valuation :=
    localCompleteDVFValuation_hasExtension ℚ_[p] D
  let : padicBase.valuation.HasExtension coefficient.valuation :=
    padicCompletedUnramifiedValuation_hasExtension p
  let : coefficient.valuation.HasExtension ambient.valuation :=
    padicCompletedLevelCompleteDVF_hasExtension p n
  let : padicBase.valuation.HasExtension ambient.valuation :=
    ValuationTheory.DiscreteValuationField.Valuation.hasExtension_trans
      padicBase.valuation coefficient.valuation
      ambient.valuation
  let :
      canonicalBase.valuation.HasExtension ambient.valuation :=
    localCompleteDVFValuation_hasExtension_of_padicLocalField
      p ambient.valuation
  let inclusion : D →+* E := D.val.toRingHom
  have inclusion_comp : inclusion.comp (algebraMap ℚ_[p] D) = algebraMap ℚ_[p] E :=
    RingHom.ext fun x => D.val.commutes x
  let :
      canonicalBase.valuation.HasExtension
        (ambient.valuation.comap inclusion) :=
    hasExtension_comap_of_algebraMap_compatible
      inclusion inclusion_comp
  have hEquiv :
      (localCompleteDVF D).valuation.IsEquiv
        (ambient.valuation.comap inclusion) :=
    valuation_isEquiv_of_finite_separable
      canonicalBase (localCompleteDVF D)
        (ambient.valuation.comap inclusion)
  exact
    residueFieldMapOfIsEquivComap
      (localCompleteDVF D).valuation ambient.valuation
      inclusion hEquiv

/-- The residue field of the finite standard/changed compositum embeds into
the residue field of the ambient completed Lubin--Tate level. -/
noncomputable def
    padicCompletedStandardChangedCompositumResidueEmbedding
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    let M := padicCompletedStandardChangedCompositum p u n
    letI : NontriviallyNormedField M :=
      finiteExtensionSpectralNormedField ℚ_[p] M
    letI : ValuativeRel M :=
      finiteExtensionSpectralValuativeRel ℚ_[p] M
    let : IsNonarchimedeanLocalField M :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
    IsLocalRing.ResidueField
        (localCompleteDVF M).valuationSubring →+*
      IsLocalRing.ResidueField
        (padicCompletedLevelCompleteDVF p n).valuationSubring := by
  let M := padicCompletedStandardChangedCompositum p u n
  let E := padicCompletedLevelField p n
  let padicBase := (padicLocalField p).toCompleteDVF
  let canonicalBase := localCompleteDVF ℚ_[p]
  let coefficient := padicCompletedUnramifiedCompleteDVF p
  let ambient := padicCompletedLevelCompleteDVF p n
  letI : NontriviallyNormedField M :=
    finiteExtensionSpectralNormedField ℚ_[p] M
  letI : ValuativeRel M :=
    finiteExtensionSpectralValuativeRel ℚ_[p] M
  let : IsNonarchimedeanLocalField M :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
  let :
      Valuation.HasExtension (ValuativeRel.valuation ℚ_[p])
        (ValuativeRel.valuation M) :=
    finiteExtensionSpectralValuation_hasExtension ℚ_[p] M
  let :
      canonicalBase.valuation.HasExtension
        (localCompleteDVF M).valuation :=
    localCompleteDVFValuation_hasExtension ℚ_[p] M
  let : padicBase.valuation.HasExtension coefficient.valuation :=
    padicCompletedUnramifiedValuation_hasExtension p
  let : coefficient.valuation.HasExtension ambient.valuation :=
    padicCompletedLevelCompleteDVF_hasExtension p n
  let : padicBase.valuation.HasExtension ambient.valuation :=
    ValuationTheory.DiscreteValuationField.Valuation.hasExtension_trans
      padicBase.valuation coefficient.valuation
      ambient.valuation
  let :
      canonicalBase.valuation.HasExtension ambient.valuation :=
    localCompleteDVFValuation_hasExtension_of_padicLocalField
      p ambient.valuation
  let inclusion : M →+* E := M.val.toRingHom
  have inclusion_comp : inclusion.comp (algebraMap ℚ_[p] M) = algebraMap ℚ_[p] E :=
    RingHom.ext fun x => M.val.commutes x
  let :
      canonicalBase.valuation.HasExtension
        (ambient.valuation.comap inclusion) :=
    hasExtension_comap_of_algebraMap_compatible
      inclusion inclusion_comp
  have hEquiv :
      (localCompleteDVF M).valuation.IsEquiv
        (ambient.valuation.comap inclusion) :=
    valuation_isEquiv_of_finite_separable
      canonicalBase (localCompleteDVF M)
        (ambient.valuation.comap inclusion)
  exact
    residueFieldMapOfIsEquivComap
      (localCompleteDVF M).valuation ambient.valuation
      inclusion hEquiv

/-- The ambient residue comparison for the finite standard/changed
compositum is injective. -/
theorem
    padicCompletedStandardChangedCompositumResidueEmbedding_injective
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    Function.Injective
      (padicCompletedStandardChangedCompositumResidueEmbedding
        p u n) :=
  (padicCompletedStandardChangedCompositumResidueEmbedding
    p u n).injective

/-- The finite standard/changed compositum is finite-dimensional over its
changed-uniformizer fixed subfield. -/
noncomputable instance
    padicCompletedStandardChangedCompositum_finiteDimensional_over_changedField
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    FiniteDimensional
      (padicCompletedChangedUniformizerFixedField p u n)
      (padicCompletedStandardChangedCompositum p u n) :=
  FiniteDimensional.right ℚ_[p]
    (padicCompletedChangedUniformizerFixedField p u n)
    (padicCompletedStandardChangedCompositum p u n)

/-- The finite standard/changed compositum is Galois over its changed fixed
subfield. -/
noncomputable instance
    padicCompletedStandardChangedCompositum_isGalois_over_changedField
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IsGalois
      (padicCompletedChangedUniformizerFixedField p u n)
      (padicCompletedStandardChangedCompositum p u n) :=
  IsGalois.tower_top_of_isGalois ℚ_[p]
    (padicCompletedChangedUniformizerFixedField p u n)
    (padicCompletedStandardChangedCompositum p u n)

/-- The changed fixed field carries its canonical finite-extension spectral
norm. -/
noncomputable instance
    padicCompletedChangedUniformizerFixedFieldNontriviallyNormedField
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    NontriviallyNormedField
      (padicCompletedChangedUniformizerFixedField p u n) :=
  finiteExtensionSpectralNormedField ℚ_[p]
    (padicCompletedChangedUniformizerFixedField p u n)

/-- The standard/changed compositum carries its canonical finite-extension
spectral norm. -/
noncomputable instance
    padicCompletedStandardChangedCompositumNontriviallyNormedField
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    NontriviallyNormedField
      (padicCompletedStandardChangedCompositum p u n) :=
  finiteExtensionSpectralNormedField ℚ_[p]
    (padicCompletedStandardChangedCompositum p u n)

/-- The changed fixed field has the canonical valuative relation induced by
its finite p-adic spectral norm. -/
noncomputable instance
    padicCompletedChangedUniformizerFixedFieldValuativeRel
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    ValuativeRel
      (padicCompletedChangedUniformizerFixedField p u n) :=
  finiteExtensionSpectralValuativeRel ℚ_[p]
    (padicCompletedChangedUniformizerFixedField p u n)

/-- The standard/changed compositum has the canonical valuative relation
induced by its finite p-adic spectral norm. -/
noncomputable instance
    padicCompletedStandardChangedCompositumValuativeRel
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    ValuativeRel
      (padicCompletedStandardChangedCompositum p u n) :=
  finiteExtensionSpectralValuativeRel ℚ_[p]
    (padicCompletedStandardChangedCompositum p u n)

/-- The changed fixed field is a nonarchimedean local field for its canonical
finite p-adic spectral topology. -/
noncomputable instance
    padicCompletedChangedUniformizerFixedField_isNonarchimedeanLocalField
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IsNonarchimedeanLocalField
      (padicCompletedChangedUniformizerFixedField p u n) :=
  finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p]
    (padicCompletedChangedUniformizerFixedField p u n)

/-- The standard/changed compositum is a nonarchimedean local field for its
canonical finite p-adic spectral topology. -/
noncomputable instance
    padicCompletedStandardChangedCompositum_isNonarchimedeanLocalField
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IsNonarchimedeanLocalField
      (padicCompletedStandardChangedCompositum p u n) :=
  finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p]
    (padicCompletedStandardChangedCompositum p u n)

/-- The canonical spectral valuation of the standard/changed compositum
extends that of the changed fixed field. -/
noncomputable instance
    padicCompletedStandardChangedCompositum_valuation_hasExtension
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    Valuation.HasExtension
      (ValuativeRel.valuation
        (padicCompletedChangedUniformizerFixedField p u n))
      (ValuativeRel.valuation
        (padicCompletedStandardChangedCompositum p u n)) :=
  finiteExtensionSpectralValuation_hasExtension_of_tower ℚ_[p]
    (padicCompletedChangedUniformizerFixedField p u n)
    (padicCompletedStandardChangedCompositum p u n)

/-- The canonical complete-DVF valuation of the standard/changed compositum
extends the one on the changed fixed field. -/
noncomputable instance
    padicCompletedStandardChangedCompositum_localCompleteDVFValuation_hasExtension
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    (localCompleteDVF
      (padicCompletedChangedUniformizerFixedField p u n)).valuation.HasExtension
      (localCompleteDVF
        (padicCompletedStandardChangedCompositum p u n)).valuation :=
  localCompleteDVFValuation_hasExtension
    (padicCompletedChangedUniformizerFixedField p u n)
    (padicCompletedStandardChangedCompositum p u n)

/-- The canonical valuation ring of the standard/changed compositum is the
integral closure of that of the changed fixed field. -/
noncomputable instance
    padicCompletedStandardChangedCompositum_valuationSubring_isIntegralClosure
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IsIntegralClosure
      (localCompleteDVF
        (padicCompletedStandardChangedCompositum p u n)).valuationSubring
      (localCompleteDVF
        (padicCompletedChangedUniformizerFixedField p u n)).valuationSubring
      (padicCompletedStandardChangedCompositum p u n) :=
  target_valuationSubring_isIntegralClosure_of_finite_separable
    (localCompleteDVF
      (padicCompletedChangedUniformizerFixedField p u n))
    (localCompleteDVF
      (padicCompletedStandardChangedCompositum p u n))

/-- The actual valuative integer ring of the standard/changed compositum is
the integral closure of the actual valuative integer ring of the changed
fixed field. -/
noncomputable instance
    padicCompletedStandardChangedCompositum_integerRing_isIntegralClosure
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IsIntegralClosure
      𝒪[padicCompletedStandardChangedCompositum p u n]
      𝒪[padicCompletedChangedUniformizerFixedField p u n]
      (padicCompletedStandardChangedCompositum p u n) := by
  have h :=
    padicCompletedStandardChangedCompositum_valuationSubring_isIntegralClosure
      p u n
  change IsIntegralClosure
    (localCompleteDVF
      (padicCompletedStandardChangedCompositum p u n)).valuation.valuationSubring
    (localCompleteDVF
      (padicCompletedChangedUniformizerFixedField p u n)).valuation.valuationSubring
    (padicCompletedStandardChangedCompositum p u n) at h
  rw [localCompleteDVF_valuation_eq,
    localCompleteDVF_valuation_eq] at h
  exact h

/-- Under the ambient residue embedding, the residue action of the finite
relative Artin candidate is the residue action of inverse completed
Frobenius. -/
theorem
    padicCompletedStandardChangedCompositumResidueEmbedding_artinCandidate
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)
    (a : IsLocalRing.ResidueField
      (localCompleteDVF
        (padicCompletedStandardChangedCompositum p u n)).valuationSubring) :
    padicCompletedStandardChangedCompositumResidueEmbedding p u n
        (galoisGroupResidueFieldEquivOfIsIntegralClosure
          (padicCompletedChangedUniformizerFixedField p u n)
          (padicCompletedStandardChangedCompositum p u n)
          (padicCompletedChangedUniformizerRelativeArtinCandidate
            p u n) a) =
      IsLocalRing.ResidueField.mapEquiv
          (padicCompletedUnitFrobeniusIntegerEquiv p n u⁻¹).symm
        (padicCompletedStandardChangedCompositumResidueEmbedding
          p u n a) := by
  let D := padicCompletedChangedUniformizerFixedField p u n
  let M := padicCompletedStandardChangedCompositum p u n
  let E := padicCompletedLevelField p n
  let padicBase := (padicLocalField p).toCompleteDVF
  let canonicalBase := localCompleteDVF ℚ_[p]
  let coefficient := padicCompletedUnramifiedCompleteDVF p
  let ambient := padicCompletedLevelCompleteDVF p n
  let :
      Valuation.HasExtension (ValuativeRel.valuation ℚ_[p])
        (ValuativeRel.valuation M) :=
    finiteExtensionSpectralValuation_hasExtension ℚ_[p] M
  let :
      canonicalBase.valuation.HasExtension
        (localCompleteDVF M).valuation :=
    localCompleteDVFValuation_hasExtension ℚ_[p] M
  let : padicBase.valuation.HasExtension coefficient.valuation :=
    padicCompletedUnramifiedValuation_hasExtension p
  let : coefficient.valuation.HasExtension ambient.valuation :=
    padicCompletedLevelCompleteDVF_hasExtension p n
  let : padicBase.valuation.HasExtension ambient.valuation :=
    ValuationTheory.DiscreteValuationField.Valuation.hasExtension_trans
      padicBase.valuation coefficient.valuation
      ambient.valuation
  let :
      canonicalBase.valuation.HasExtension ambient.valuation :=
    localCompleteDVFValuation_hasExtension_of_padicLocalField
      p ambient.valuation
  let inclusion : M →+* E := M.val.toRingHom
  have inclusion_comp : inclusion.comp (algebraMap ℚ_[p] M) = algebraMap ℚ_[p] E :=
    RingHom.ext fun x => M.val.commutes x
  let :
      canonicalBase.valuation.HasExtension
        (ambient.valuation.comap inclusion) :=
    hasExtension_comap_of_algebraMap_compatible
      inclusion inclusion_comp
  have hEquiv :
      (localCompleteDVF M).valuation.IsEquiv
        (ambient.valuation.comap inclusion) :=
    valuation_isEquiv_of_finite_separable
      canonicalBase (localCompleteDVF M)
        (ambient.valuation.comap inclusion)
  let τ :=
    padicCompletedChangedUniformizerRelativeArtinCandidate p u n
  let σM :
      (localCompleteDVF M).valuationSubring ≃+*
        (localCompleteDVF M).valuationSubring :=
    galoisGroupIntegerRingEquivOfIsIntegralClosure D M τ
  let σE :
      ambient.valuationSubring ≃+* ambient.valuationSubring :=
    (padicCompletedUnitFrobeniusIntegerEquiv p n u⁻¹).symm
  have hcompat :
      ∀ b : (localCompleteDVF M).valuationSubring,
        valuationSubringMapOfIsEquivComap
            (localCompleteDVF M).valuation ambient.valuation
            inclusion hEquiv (σM b) =
          σE
            (valuationSubringMapOfIsEquivComap
              (localCompleteDVF M).valuation ambient.valuation
              inclusion hEquiv b) := by
    intro b
    apply Subtype.ext
    change
      M.val (τ (b : M)) =
        (padicCompletedUnitFrobeniusLiftEquiv p n u⁻¹).symm
          (M.val (b : M))
    rfl
  change
    residueFieldMapOfIsEquivComap
        (localCompleteDVF M).valuation ambient.valuation
        inclusion hEquiv
        (IsLocalRing.ResidueField.mapEquiv σM a) =
      IsLocalRing.ResidueField.mapEquiv σE
        (residueFieldMapOfIsEquivComap
          (localCompleteDVF M).valuation ambient.valuation
          inclusion hEquiv a)
  exact
    residueFieldMapOfIsEquivComap_mapEquiv
      (localCompleteDVF M).valuation ambient.valuation
      inclusion hEquiv σM σE hcompat a

end LubinTate

end
