/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianConductorRamification
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianLocalConductorComparison
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorInfinitePart
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertNormCharacterization
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteLocalGlobalArtinCompatibility
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.SeparableClosurePadicLift
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.FinitePadicCyclicData
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.FinitePadicAuxiliaryField
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.Factorization
/-!
# Exact finite ramification loci for abelian norm data

For a finite abelian extension, the modulus constructed from the
actual chosen local norm groups has support exactly the ramified finite
places.  At the archimedean places, the determinant-norm image is the
whole local multiplicative group exactly when the extension is
unramified at infinity.

The finite statement is deliberately about the locally constructed
norm modulus.  Identifying it with the minimal narrow finite conductor also
requires the compatibility between the actual global norm-residue map
and the chosen local Artin map on one-place ideles.
-/

open scoped NumberField Classical NumberField.LiesOver

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open LocalClassFieldTheory LocalFieldTheory
open NumberField IsDedekindDomain

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

private theorem
    finitePlaceIdeleClass_mem_normRange_of_mem_narrowFiniteHigherUnit
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ)
    (hx :
      x ∈ RayClass.localHigherUnitGroup v
        (ideleClassNormNarrowFiniteConductor
          (K := K) (L := L) v)) :
    IdeleGroup.finitePlaceIdeleClass v x ∈
      (_root_.ideleClassNorm K L).range := by
  apply
    ideleClassNorm_narrowFiniteConductor_isDefiningModulus
      (K := K) (L := L)
  apply
    RayClass.localHigherUnitClassSubgroup_le_congruenceSubgroup
      (RayClass.Modulus.narrowOfFinite
        (ideleClassNormNarrowFiniteConductor
          (K := K) (L := L))) v
  refine ⟨x, ?_, rfl⟩
  change
    x ∈ RayClass.localHigherUnitGroup v
      (ideleClassNormNarrowFiniteConductor
        (K := K) (L := L) v)
  exact hx

private theorem
    narrowFiniteHigherUnitGroup_le_chosenFinitePlaceLocalNormSubgroup
    (v : HeightOneSpectrum (𝓞 K)) :
    RayClass.localHigherUnitGroup v
        (ideleClassNormNarrowFiniteConductor
          (K := K) (L := L) v) ≤
      _root_.chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v := by
  intro x hx
  apply
    (Reciprocity.chosenFinitePlaceArtinMonoidHom_eq_one_iff_chosenLocalNorm
      (K := K) (L := L) v x).1
  have hglobal :
      Reciprocity.globalNormResidueMonoidHom K L
          (IdeleGroup.finitePlaceIdeleClass v x) = 1 :=
    (Reciprocity.globalNormResidueMonoidHom_eq_one_iff
      K L (IdeleGroup.finitePlaceIdeleClass v x)).2
      (finitePlaceIdeleClass_mem_normRange_of_mem_narrowFiniteHigherUnit
        (K := K) (L := L) v x hx)
  have hcompat :
      Reciprocity.globalNormResidueMonoidHom K L
          (IdeleGroup.finitePlaceIdeleClass v x) =
        Reciprocity.chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v x :=
    DFunLike.congr_fun
      (Reciprocity.globalNormResidueMonoidHom_comp_finitePlaceIdeleClass
        (K := K) (L := L) v) x
  exact hcompat.symm.trans hglobal

/-- The modulus obtained from the actual chosen local norm groups is
bounded by the minimal narrow finite conductor.  The substantive input is the
finite-place local--global compatibility theorem: a one-place idele
class is a global class norm exactly when its local component is a norm
from the chosen completion. -/
theorem ideleClassNormDefiningModulus_le_narrowFiniteConductor :
    ideleClassNormDefiningModulus (K := K) (L := L) ≤
      ideleClassNormNarrowFiniteConductor (K := K) (L := L) := by
  exact
    ideleClassNormDefiningModulus_le_of_localHigherUnitGroup_le
      (K := K) (L := L)
      (ideleClassNormNarrowFiniteConductor (K := K) (L := L))
      (narrowFiniteHigherUnitGroup_le_chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L))

/-- The minimal narrow finite conductor of an actual finite abelian extension
is exactly the modulus obtained from its actual chosen local norm
groups. -/
theorem ideleClassNorm_narrowFiniteConductor_eq_normDefiningModulus :
    ideleClassNormNarrowFiniteConductor (K := K) (L := L) =
      ideleClassNormDefiningModulus (K := K) (L := L) :=
  le_antisymm
    (ideleClassNorm_narrowFiniteConductor_le_normDefiningModulus
      (K := K) (L := L))
    (ideleClassNormDefiningModulus_le_narrowFiniteConductor
      (K := K) (L := L))

/-- At every finite place, the corresponding exponent of the minimal
narrow finite conductor is exactly the local conductor exponent of the
genuine chosen localized extension.  Thus the narrow finite conductor is
the finite product of its actual local conductors, encoded pointwise in
`RayClass.Modulus`. -/
theorem
    ideleClassNorm_narrowFiniteConductor_apply_eq_chosenLocalConductorExponent
    (v : HeightOneSpectrum (𝓞 K)) :
    ideleClassNormNarrowFiniteConductor (K := K) (L := L) v =
      ideleClassNormChosenFinitePlaceLocalConductorExponent
        (K := K) (L := L) v := by
  calc
    ideleClassNormNarrowFiniteConductor (K := K) (L := L) v =
        ideleClassNormDefiningModulus (K := K) (L := L) v := by
      rw [ideleClassNorm_narrowFiniteConductor_eq_normDefiningModulus]
    _ =
        ideleClassNormLocalHigherUnitExponent
          (K := K) (L := L) v :=
      ideleClassNormDefiningModulus_apply
        (K := K) (L := L) v
    _ =
        ideleClassNormChosenFinitePlaceLocalConductorExponent
          (K := K) (L := L) v :=
      ideleClassNormLocalHigherUnitExponent_eq_localConductorExponent
        (K := K) (L := L) v

/-- For a finite abelian extension, the support of the modulus obtained
from the actual chosen local norm subgroups is precisely the set of
ramified finite places of the base field. -/
theorem
    ideleClassNormDefiningModulus_support_eq_ramifiedBaseFinitePlaces :
    (ideleClassNormDefiningModulus
        (K := K) (L := L)).support =
      _root_.ramifiedBaseFinitePlaces
        (K := K) (L := L) := by
  ext v
  rw [
    mem_ideleClassNormDefiningModulus_support_iff_not_chosenFinitePlaceIsUnramified,
    _root_.mem_ramifiedBaseFinitePlaces_iff]
  constructor
  · intro hramified
    let w :=
      _root_.chosenFinitePlaceExtension
        (L := L) v
    let W :=
      _root_.finitePlaceExtensionCentre
        (K := K) (L := L) v w
    refine
      ⟨W,
        _root_.finitePlaceExtensionCentre_liesOver
          (K := K) (L := L) v w, ?_⟩
    intro hW
    exact
      hramified
        (_root_.chosenFinitePlaceIsUnramified_of_isUnramifiedAt
          (K := K) (L := L) v hW)
  · rintro ⟨P, hP, hP_ramified⟩ hchosen
    apply hP_ramified
    apply
      _root_.isUnramifiedAt_at_finitePlaceAbove_of_chosenFinitePlaceIsUnramified
        (K := K) (L := L) v P
    · apply HeightOneSpectrum.ext
      exact hP.over.symm
    · exact hchosen

/-- The actual local norm modulus vanishes exactly when no finite base
place ramifies. -/
theorem
    ideleClassNormDefiningModulus_eq_zero_iff_ramifiedBaseFinitePlaces_eq_empty :
    ideleClassNormDefiningModulus (K := K) (L := L) = 0 ↔
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅ := by
  rw [
    ← Finsupp.support_eq_empty,
    ideleClassNormDefiningModulus_support_eq_ramifiedBaseFinitePlaces]

/-- The actual local norm modulus vanishes exactly when the extension
is unramified at every finite place upstairs. -/
theorem
    ideleClassNormDefiningModulus_eq_zero_iff_all_finitePlaces_unramified :
    ideleClassNormDefiningModulus (K := K) (L := L) = 0 ↔
      ∀ P : HeightOneSpectrum (𝓞 L),
        Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal := by
  rw [
    ideleClassNormDefiningModulus_eq_zero_iff_ramifiedBaseFinitePlaces_eq_empty]
  constructor
  · intro hempty P
    by_contra hP
    have hramified :
        _root_.finitePlaceBelow (K := K) P ∈
          _root_.ramifiedBaseFinitePlaces
            (K := K) (L := L) := by
      rw [_root_.mem_ramifiedBaseFinitePlaces_iff]
      refine ⟨P, ?_, hP⟩
      exact ⟨by simp only [_root_.finitePlaceBelow_asIdeal]⟩
    exact
      (Finset.eq_empty_iff_forall_notMem.mp hempty
        (_root_.finitePlaceBelow (K := K) P)) hramified
  · intro hunramified
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    rw [_root_.mem_ramifiedBaseFinitePlaces_iff] at hv
    obtain ⟨P, _hP, hP_ramified⟩ := hv
    exact hP_ramified (hunramified P)

/-- The support of the minimal narrow finite conductor of a finite abelian
extension is exactly its finite ramification locus. -/
theorem
    ideleClassNorm_narrowFiniteConductor_support_eq_ramifiedBaseFinitePlaces :
    (ideleClassNormNarrowFiniteConductor
      (K := K) (L := L)).support =
      _root_.ramifiedBaseFinitePlaces
        (K := K) (L := L) := by
  rw [
    ideleClassNorm_narrowFiniteConductor_eq_normDefiningModulus,
    ideleClassNormDefiningModulus_support_eq_ramifiedBaseFinitePlaces]

/-- The minimal narrow finite conductor vanishes exactly when the extension
is unramified at every finite place upstairs. -/
theorem
    ideleClassNorm_narrowFiniteConductor_eq_zero_iff_all_finitePlaces_unramified :
    ideleClassNormNarrowFiniteConductor (K := K) (L := L) = 0 ↔
      ∀ P : HeightOneSpectrum (𝓞 L),
        Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal := by
  rw [
    ideleClassNorm_narrowFiniteConductor_eq_normDefiningModulus,
    ideleClassNormDefiningModulus_eq_zero_iff_all_finitePlaces_unramified]

omit [FiniteDimensional K L] in
/-- A ramified real-to-complex completion makes the corresponding
archimedean tensor norm subgroup proper. -/
private theorem infiniteTensorNormSubgroup_ne_top_of_isRamified
    (v : InfinitePlace K)
    (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v)
    (hramified : w.IsRamified K) :
    _root_.infiniteTensorNormSubgroup
      (K := K) (L := L) v ≠ ⊤ := by
  let : w.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
  rw [
    _root_.infiniteTensorNormSubgroup_eq_localNormSubgroup
      (K := K) (L := L) v w hw]
  have hvReal : v.IsReal := by
    rw [← hw]
    exact hramified.isReal
  let eRealField :
      v.Completion ≃+* ℝ :=
    InfinitePlace.Completion.ringEquivRealOfIsReal
      hvReal
  let eRealUnits :
      v.Completionˣ ≃* ℝˣ :=
    Units.mapEquiv eRealField.toMulEquiv
  have hwComplex : w.IsComplex :=
    hramified.isComplex
  let eComplexField :
      w.Completion ≃+* ℂ :=
    InfinitePlace.Completion.ringEquivComplexOfIsComplex
      hwComplex
  let eComplexUnits :
      w.Completionˣ ≃* ℂˣ :=
    Units.mapEquiv eComplexField.toMulEquiv
  let :
      NumberField.ComplexEmbedding.LiesOver
        (InfinitePlace.Completion.extensionEmbedding w)
        (InfinitePlace.Completion.extensionEmbedding v) :=
    InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal
      w hvReal
  have hCompletionCompatible :
      RingHom.comp (algebraMap ℝ ℂ) eRealField =
        RingHom.comp eComplexField
          (algebraMap v.Completion w.Completion) := by
    ext x
    change
      (InfinitePlace.Completion.extensionEmbeddingOfIsReal hvReal x : ℂ) =
        InfinitePlace.Completion.extensionEmbedding w
          ((algebraMap v.Completion w.Completion) x)
    rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
    exact
      (InfinitePlace.Completion.liesOver_extensionEmbedding_apply
        w (v := v)).symm
  have hCompletionCompatibleSymm :=
    LocalClassFieldTheory.ringEquiv_compat_symm
      eRealField eComplexField hCompletionCompatible
  have hRealComplexNormTransport :
      (localNormSubgroup ℝ ℂ).map
          eRealUnits.symm.toMonoidHom =
        localNormSubgroup
          v.Completion w.Completion := by
    ext x
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      refine ⟨eComplexUnits.symm z, ?_⟩
      exact
        (LocalClassFieldTheory.normUnits_map_ringEquiv
          eRealField.symm eComplexField.symm
          hCompletionCompatibleSymm z).symm
    · rintro ⟨z, rfl⟩
      refine
        ⟨normUnits ℝ ℂ (eComplexUnits z),
          ⟨eComplexUnits z, rfl⟩, ?_⟩
      calc
        eRealUnits.symm
            (normUnits ℝ ℂ (eComplexUnits z)) =
            normUnits v.Completion w.Completion
              (eComplexUnits.symm (eComplexUnits z)) := by
          exact
            LocalClassFieldTheory.normUnits_map_ringEquiv
              eRealField.symm eComplexField.symm
              hCompletionCompatibleSymm
              (eComplexUnits z)
        _ = normUnits v.Completion w.Completion z := by
          rw [eComplexUnits.symm_apply_apply]
  have hNegativeOne :
      (-1 : ℝˣ) ∉ localNormSubgroup ℝ ℂ := by
    rw [
      ← LocalClassFieldTheory.realUnitsSign_ker_eq_complexNormSubgroup,
      LocalClassFieldTheory.mem_realUnitsSign_ker_iff]
    norm_num
  intro htop
  have hx :
      eRealUnits.symm (-1 : ℝˣ) ∈
        localNormSubgroup v.Completion w.Completion := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [← hRealComplexNormTransport] at hx
  obtain ⟨z, hz, hzEq⟩ := hx
  have hzNegativeOne : z = (-1 : ℝˣ) :=
    eRealUnits.symm.injective hzEq
  exact hNegativeOne (hzNegativeOne ▸ hz)

omit [FiniteDimensional K L] in
/-- At a base infinite place, the determinant-norm image is the whole
local multiplicative group exactly when the extension is unramified
above that place. -/
theorem infiniteTensorNormSubgroup_eq_top_iff_isUnramifiedIn
    (v : InfinitePlace K) :
    _root_.infiniteTensorNormSubgroup
          (K := K) (L := L) v = ⊤ ↔
      v.IsUnramifiedIn L := by
  obtain ⟨w, hw⟩ :=
    InfinitePlace.comap_surjective
      (K := L) v
  have hUnramified :
      v.IsUnramifiedIn L ↔ w.IsUnramified K := by
    rw [← hw, InfinitePlace.isUnramifiedIn_comap]
  rw [hUnramified]
  constructor
  · intro htop
    by_contra hramified
    have hRamified : w.IsRamified K :=
      hramified
    exact
      (infiniteTensorNormSubgroup_ne_top_of_isRamified
        (K := K) (L := L) v w hw hRamified)
        htop
  · intro hunramified
    let : w.1.LiesOver v.1 :=
      ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
    rw [
      _root_.infiniteTensorNormSubgroup_eq_localNormSubgroup
        (K := K) (L := L) v w hw]
    apply top_unique
    intro x _
    refine
      ⟨Units.map
          (algebraMap
            v.Completion w.Completion).toMonoidHom x, ?_⟩
    apply Units.ext
    change
      Algebra.norm v.Completion
          (algebraMap v.Completion w.Completion
            (x : v.Completion)) =
        (x : v.Completion)
    rw [
      Algebra.norm_algebraMap,
      InfinitePlace.IsUnramified.finrank_eq_one
        v hunramified,
      pow_one]

/-- The infinite part of the full conductor of an idèle-class norm range is
exactly the set of ramified real places. -/
theorem ideleClassNormFullConductor_infinitePart_eq_realRamificationLocus :
    (ideleClassNormConductorialSubgroup
        (K := K) (L := L)).fullConductor.infinitePart =
      (Finset.univ.filter fun v : RayClass.RealPlace K =>
        ¬ v.1.IsUnramifiedIn L) := by
  classical
  ext v
  change
    v ∈ (ideleClassNormConductorialSubgroup
        (K := K) (L := L)).fullConductorInfinitePart ↔
      v ∈ (Finset.univ.filter fun w : RayClass.RealPlace K =>
        ¬ w.1.IsUnramifiedIn L)
  rw [ConductorialSubgroup.mem_fullConductorInfinitePart_iff,
    Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  change
    (¬ (IdeleGroup.infinitePlaceIdeleClass v.1).range ≤
        (_root_.ideleClassNorm K L).range) ↔
      ¬ v.1.IsUnramifiedIn L
  apply not_congr
  calc
    (IdeleGroup.infinitePlaceIdeleClass v.1).range ≤
          (_root_.ideleClassNorm K L).range ↔
        _root_.infiniteTensorNormSubgroup
            (K := K) (L := L) v.1 = ⊤ := by
      constructor
      · intro hRange
        apply top_unique
        intro x _hx
        apply
          (Reciprocity.infinitePlaceIdeleClass_mem_ideleClassNorm_range_iff
            (K := K) (L := L) v.1 x).1
        exact hRange ⟨x, rfl⟩
      · intro hTop
        rintro _ ⟨x, rfl⟩
        apply
          (Reciprocity.infinitePlaceIdeleClass_mem_ideleClassNorm_range_iff
            (K := K) (L := L) v.1 x).2
        rw [hTop]
        exact Subgroup.mem_top x
    _ ↔ v.1.IsUnramifiedIn L :=
      infiniteTensorNormSubgroup_eq_top_iff_isUnramifiedIn
        (K := K) (L := L) v.1

omit [FiniteDimensional K L] in
/-- A finite abelian number-field extension is unramified at every
infinite place exactly when every archimedean tensor determinant-norm
image is the whole local multiplicative group. -/
theorem
    infiniteTensorNormSubgroups_eq_top_iff_isUnramifiedAtInfinitePlaces :
    (∀ v : InfinitePlace K,
        _root_.infiniteTensorNormSubgroup
          (K := K) (L := L) v = ⊤) ↔
      IsUnramifiedAtInfinitePlaces K L := by
  constructor
  · intro htop
    exact
      ⟨fun w =>
        (infiniteTensorNormSubgroup_eq_top_iff_isUnramifiedIn
          (K := K) (L := L)
          (w.comap (algebraMap K L))).1
          (htop (w.comap (algebraMap K L))) w rfl⟩
  · intro hunramified
    let : IsUnramifiedAtInfinitePlaces K L :=
      hunramified
    exact fun v =>
      infiniteTensorNormSubgroup_eq_top_of_isUnramifiedAtInfinitePlaces
        (K := K) (L := L) v

/-- In the repository's modulus convention, the finite conductor is
zero and every archimedean determinant-norm image is the full local
group exactly when the extension is unramified at every finite and
infinite place.

This combines the finite support of the narrow finite conductor with the
separate archimedean clause, so no ramification place is omitted by
the fact that `RayClass.Modulus` records only finite exponents. -/
theorem
    ideleClassNorm_everywhereUnramified_iff_conductor_zero_and_infiniteNorms_top :
    ((∀ P : HeightOneSpectrum (𝓞 L),
          Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal) ∧
        IsUnramifiedAtInfinitePlaces K L) ↔
      (ideleClassNormNarrowFiniteConductor
            (K := K) (L := L) = 0 ∧
        ∀ v : InfinitePlace K,
          _root_.infiniteTensorNormSubgroup
            (K := K) (L := L) v = ⊤) := by
  rw [
    ideleClassNorm_narrowFiniteConductor_eq_zero_iff_all_finitePlaces_unramified,
    infiniteTensorNormSubgroups_eq_top_iff_isUnramifiedAtInfinitePlaces]

end GlobalClassFields
end GlobalClassFieldTheory

namespace ClassFieldTheory

open NumberField IsDedekindDomain

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The finite exponent of the full norm conductor is the local conductor
exponent at the chosen completion above the place. -/
theorem abelianFullConductor_finiteExponent_eq_localConductorExponent
    (v : HeightOneSpectrum (𝓞 K)) :
    (GlobalClassFieldTheory.GlobalClassFields.ideleClassNormConductorialSubgroup
        (K := K) (L := L)).fullConductor.finitePart v =
      GlobalClassFieldTheory.GlobalClassFields.ideleClassNormChosenFinitePlaceLocalConductorExponent
        (K := K) (L := L) v := by
  change
    GlobalClassFieldTheory.GlobalClassFields.ideleClassNormNarrowFiniteConductor
        (K := K) (L := L) v = _
  exact
    GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_narrowFiniteConductor_apply_eq_chosenLocalConductorExponent
      (K := K) (L := L) v

/-- A finite place has conductor exponent zero precisely when the chosen
local extension is unramified. -/
theorem abelianFullConductor_finiteExponent_eq_zero_iff_unramified
    (v : HeightOneSpectrum (𝓞 K)) :
    (GlobalClassFieldTheory.GlobalClassFields.ideleClassNormConductorialSubgroup
        (K := K) (L := L)).fullConductor.finitePart v = 0 ↔
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v := by
  rw [abelianFullConductor_finiteExponent_eq_localConductorExponent]
  rw [← GlobalClassFieldTheory.GlobalClassFields.ideleClassNormLocalHigherUnitExponent_eq_localConductorExponent
    (K := K) (L := L) v]
  exact
    GlobalClassFieldTheory.GlobalClassFields.ideleClassNormLocalHigherUnitExponent_eq_zero_iff_chosenFinitePlaceIsUnramified
      (K := K) (L := L) v

/-- A real place belongs to the full norm conductor exactly when it
ramifies, equivalently complexifies, in the extension. -/
theorem abelianFullConductor_mem_infinitePart_iff_realRamified
    (v : RayClass.RealPlace K) :
    v ∈
        (GlobalClassFieldTheory.GlobalClassFields.ideleClassNormConductorialSubgroup
          (K := K) (L := L)).fullConductor.infinitePart ↔
      ¬ v.1.IsUnramifiedIn L := by
  rw [GlobalClassFieldTheory.GlobalClassFields.ideleClassNormFullConductor_infinitePart_eq_realRamificationLocus]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end ClassFieldTheory
