/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.InfinitePlaceTensorNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.LocalBlocks
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNormComponents
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.Group.Hom.Instances
/-!
# Archimedean Artin homomorphisms

At a ramified infinite place, the local extension is complex over
real.  Its Artin homomorphism sends the sign of a real unit to the
corresponding complex-conjugation element of the decomposition group.
At an unramified infinite place the decomposition group, and hence the
local homomorphism, is trivial.
-/

open scoped BigOperators IsMulCommutative NumberField
  NumberField.LiesOver
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open HilbertRamification
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

section Galois

variable [IsGalois K L]

open scoped Classical in
private noncomputable def ramifiedInfinitePlaceConjugation
    (w : InfinitePlace L) (hRamified : w.IsRamified K) :
    L ≃ₐ[K] L :=
  Classical.choose
    (InfinitePlace.exists_isConj_of_isRamified
      (k := K) (K := L)
      ((InfinitePlace.mk_embedding w).symm ▸ hRamified))

omit [NumberField K] [NumberField L] in
open scoped Classical in
private theorem ramifiedInfinitePlaceConjugation_isConj
    (w : InfinitePlace L) (hRamified : w.IsRamified K) :
    NumberField.ComplexEmbedding.IsConj
      (InfinitePlace.embedding w)
      (ramifiedInfinitePlaceConjugation
        (K := K) w hRamified) :=
  Classical.choose_spec
    (InfinitePlace.exists_isConj_of_isRamified
      (k := K) (K := L)
      ((InfinitePlace.mk_embedding w).symm ▸ hRamified))

omit [NumberField K] [NumberField L] in
open scoped Classical in
private theorem ramifiedInfinitePlaceConjugation_sq
    (w : InfinitePlace L) (hRamified : w.IsRamified K) :
    ramifiedInfinitePlaceConjugation
          (K := K) w hRamified *
        ramifiedInfinitePlaceConjugation
          (K := K) w hRamified =
      1 := by
  ext x
  simpa using
    NumberField.ComplexEmbedding.isConj_apply_apply
      (ramifiedInfinitePlaceConjugation_isConj
        (K := K) w hRamified) x

open scoped Classical in
/-- The archimedean Artin homomorphism associated with a specified
infinite place above the base place. -/
noncomputable def infinitePlaceArtinMonoidHomOfPlace
    (v : InfinitePlace K) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v) :
    v.Completionˣ →* (L ≃ₐ[K] L) := by
  by_cases hUnramified : w.IsUnramified K
  · exact 1
  · have hRamified : w.IsRamified K :=
      hUnramified
    have hvReal : v.IsReal := by
      rw [← hw]
      exact hRamified.isReal
    let signToGalois : ℤˣ →* (L ≃ₐ[K] L) :=
      { toFun := fun u =>
          if u = 1 then 1
          else
            ramifiedInfinitePlaceConjugation
              (K := K) w hRamified
        map_one' := ite_eq_left rfl
        map_mul' := by
          intro x y
          rcases Int.units_eq_one_or x with rfl | rfl
          · simp
          rcases Int.units_eq_one_or y with rfl | rfl
          · simp
          · simp [
              ramifiedInfinitePlaceConjugation_sq
                (K := K) w hRamified] }
    let completionUnitsEquivRealUnits :
        v.Completionˣ ≃* ℝˣ :=
      Units.mapEquiv
        (InfinitePlace.Completion.ringEquivRealOfIsReal
          hvReal).toMulEquiv
    exact
      signToGalois.comp
        (LocalClassFieldTheory.realUnitsSign.comp
          completionUnitsEquivRealUnits.toMonoidHom)

open scoped Classical in
/-- The actual local Artin homomorphism at an infinite place, using
the infinite place of `L` already chosen by the local-block API. -/
noncomputable def chosenInfinitePlaceArtinMonoidHom
    (v : InfinitePlace K) :
    v.Completionˣ →* (L ≃ₐ[K] L) :=
  infinitePlaceArtinMonoidHomOfPlace
    (K := K) (L := L) v
    (chosenInfinitePlaceAbove
      (L := L) v)
    (chosenInfinitePlaceAbove_comap
      (L := L) v)

omit [NumberField K] [NumberField L] in
open scoped Classical in
/-- At a ramified real place, the actual chosen local Artin symbol of
negative one is complex conjugation along the chosen infinite place
upstairs.  The statement exposes the intrinsic property of the Artin
value, without exposing the auxiliary conjugation chosen in its
construction. -/
theorem chosenInfinitePlaceArtinMonoidHom_neg_one_isConj_of_ramified
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    NumberField.ComplexEmbedding.IsConj
      (InfinitePlace.embedding
        (chosenInfinitePlaceAbove (L := L) v))
      (chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v (-1 : v.Completionˣ)) := by
  let w := chosenInfinitePlaceAbove (L := L) v
  have hw :
      w.comap (algebraMap K L) = v :=
    chosenInfinitePlaceAbove_comap (L := L) v
  have hvReal : v.IsReal := by
    rw [← hw]
    exact hRamified.isReal
  have hsign :
      LocalClassFieldTheory.realUnitsSign
          (Units.mapEquiv
            (InfinitePlace.Completion.ringEquivRealOfIsReal
              hvReal).toMulEquiv
            (-1 : v.Completionˣ)) =
        (-1 : ℤˣ) := by
    apply Units.ext
    simp [LocalClassFieldTheory.realUnitsSign]
  have hConj :=
    ramifiedInfinitePlaceConjugation_isConj
      (K := K) w hRamified
  change
    NumberField.ComplexEmbedding.IsConj
      (InfinitePlace.embedding w)
      (chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v (-1 : v.Completionˣ))
  have hUnramified : ¬ w.IsUnramified K := hRamified
  have hUnramified' :
      ¬ (chosenInfinitePlaceAbove (L := L) v).IsUnramified K := by
    simpa only [w] using hUnramified
  have hsignNe :
      LocalClassFieldTheory.realUnitsSign
          (Units.mapEquiv
            (InfinitePlace.Completion.ringEquivRealOfIsReal
              hvReal).toMulEquiv
            (-1 : v.Completionˣ)) ≠ 1 := by
    rw [hsign]
    decide
  unfold chosenInfinitePlaceArtinMonoidHom
  unfold infinitePlaceArtinMonoidHomOfPlace
  simp only [dite_eq_right hUnramified', MonoidHom.comp_apply]
  change
    NumberField.ComplexEmbedding.IsConj
      (InfinitePlace.embedding w)
      (if
          LocalClassFieldTheory.realUnitsSign
              (Units.mapEquiv
                (InfinitePlace.Completion.ringEquivRealOfIsReal
                  hvReal).toMulEquiv
                (-1 : v.Completionˣ)) =
            1 then
        1
      else
        ramifiedInfinitePlaceConjugation
          (K := K)
          (chosenInfinitePlaceAbove (L := L) v)
          hUnramified')
  rw [ite_eq_right hsignNe]
  simpa only [w] using hConj

end Galois

section AbelianTower

variable [IsAbelianGalois K L]

omit [NumberField K] [NumberField L] in
open scoped Classical in
/-- In an abelian extension, the archimedean Artin homomorphism is
independent of the chosen infinite place above the base place. -/
theorem infinitePlaceArtinMonoidHomOfPlace_eq
    (v : InfinitePlace K)
    (w w' : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v)
    (hw' : w'.comap (algebraMap K L) = v) :
    infinitePlaceArtinMonoidHomOfPlace
        (K := K) (L := L) v w hw =
      infinitePlaceArtinMonoidHomOfPlace
        (K := K) (L := L) v w' hw' := by
  obtain ⟨g, hg⟩ :=
    InfinitePlace.exists_smul_eq_of_comap_eq
      (hw.trans hw'.symm)
  have hUnramified :
      w.IsUnramified K ↔ w'.IsUnramified K := by
    rw [InfinitePlace.isUnramified_iff,
      InfinitePlace.isUnramified_iff, hw, hw']
    rw [← hg, InfinitePlace.isReal_smul_iff]
  by_cases hwUnramified : w.IsUnramified K
  · have hw'Unramified : w'.IsUnramified K :=
      hUnramified.mp hwUnramified
    simp [infinitePlaceArtinMonoidHomOfPlace,
      hwUnramified, hw'Unramified]
  · have hw'Unramified : ¬ w'.IsUnramified K :=
      fun h => hwUnramified (hUnramified.mpr h)
    have hwRamified : w.IsRamified K := hwUnramified
    have hw'Ramified : w'.IsRamified K := hw'Unramified
    let sigma :=
      ramifiedInfinitePlaceConjugation
        (K := K) w hwRamified
    let sigma' :=
      ramifiedInfinitePlaceConjugation
        (K := K) w' hw'Ramified
    have hsigma :=
      ramifiedInfinitePlaceConjugation_isConj
        (K := K) w hwRamified
    have hsigma' :=
      ramifiedInfinitePlaceConjugation_isConj
        (K := K) w' hw'Ramified
    have hsigmaMem :
        sigma ∈
          MulAction.stabilizer (L ≃ₐ[K] L) w := by
      rw [← InfinitePlace.mk_embedding w,
        InfinitePlace.mem_stabilizer_mk_iff]
      exact Or.inr hsigma
    have hsigmaMem' :
        sigma ∈
          MulAction.stabilizer (L ≃ₐ[K] L) w' := by
      rw [← hg]
      rw [MulAction.mem_stabilizer_iff] at hsigmaMem
      rw [MulAction.mem_stabilizer_iff]
      calc
        sigma • (g • w) =
            (sigma * g) • w :=
          (mul_smul sigma g w).symm
        _ = (g * sigma) • w := by
          rw [mul_comm]
        _ = g • (sigma • w) :=
          mul_smul g sigma w
        _ = g • w := by
          rw [hsigmaMem]
    have hsigmaNe : sigma ≠ 1 :=
      (NumberField.ComplexEmbedding.isConj_ne_one_iff
        hsigma).2
        (InfinitePlace.isComplex_iff.mp
          hwRamified.isComplex)
    have hsigmaAtW' :
        NumberField.ComplexEmbedding.IsConj
          (InfinitePlace.embedding w') sigma := by
      rw [← InfinitePlace.mk_embedding w',
        InfinitePlace.mem_stabilizer_mk_iff] at hsigmaMem'
      exact hsigmaMem'.resolve_left hsigmaNe
    have hsigmaEq : sigma = sigma' :=
      hsigmaAtW'.ext hsigma'
    apply MonoidHom.ext
    intro x
    simp [infinitePlaceArtinMonoidHomOfPlace,
      hwUnramified, hw'Unramified,
      sigma, sigma', hsigmaEq]

omit [NumberField K] [NumberField L] in
open scoped Classical in
/-- Archimedean Artin homomorphisms attached to specified places commute
with restriction through an abelian tower. -/
theorem infinitePlaceArtinMonoidHomOfPlace_restrict_tower
    {E : Type}
    [Field E]
    [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    [IsGalois K E]
    (v : InfinitePlace K)
    (wL : InfinitePlace L)
    (hwL : wL.comap (algebraMap K L) = v)
    (hwE :
      (wL.comap (algebraMap E L)).comap
          (algebraMap K E) = v) :
    (AlgEquiv.restrictNormalHom E).comp
        (infinitePlaceArtinMonoidHomOfPlace
          (K := K) (L := L) v wL hwL) =
      infinitePlaceArtinMonoidHomOfPlace
        (K := K) (L := E) v
        (wL.comap (algebraMap E L)) hwE := by
  let wE := wL.comap (algebraMap E L)
  by_cases hLUnramified : wL.IsUnramified K
  · have hEUnramified : wE.IsUnramified K :=
      hLUnramified.comap E
    simp [infinitePlaceArtinMonoidHomOfPlace,
      hLUnramified, hEUnramified, wE]
  · have hLRamified : wL.IsRamified K :=
      hLUnramified
    have hvReal : v.IsReal := by
      rw [← hwL]
      exact hLRamified.isReal
    let sigmaL :=
      ramifiedInfinitePlaceConjugation
        (K := K) wL hLRamified
    let sigmaR : E ≃ₐ[K] E :=
      AlgEquiv.restrictNormalHom E sigmaL
    have hsigmaL :=
      ramifiedInfinitePlaceConjugation_isConj
        (K := K) wL hLRamified
    let phi : E →+* ℂ :=
      (InfinitePlace.embedding wL).comp
        (algebraMap E L)
    have hphi :
        NumberField.ComplexEmbedding.IsConj
          phi sigmaR := by
      apply RingHom.ext
      intro x
      change
        star
            (InfinitePlace.embedding wL
              (algebraMap E L x)) =
          InfinitePlace.embedding wL
            (algebraMap E L (sigmaR x))
      rw [show
        algebraMap E L (sigmaR x) =
          sigmaL (algebraMap E L x) by
          dsimp [sigmaR]
          exact AlgEquiv.restrictNormal_commutes sigmaL E x]
      exact (hsigmaL.eq (algebraMap E L x)).symm
    have hmk : InfinitePlace.mk phi = wE := by
      change
        InfinitePlace.mk
            ((InfinitePlace.embedding wL).comp
              (algebraMap E L)) =
          wL.comap (algebraMap E L)
      conv_rhs => rw [← InfinitePlace.mk_embedding wL]
      rw [InfinitePlace.comap_mk]
    by_cases hEUnramified : wE.IsUnramified K
    · have hEUnramified' :
          (wL.comap (algebraMap E L)).IsUnramified K := by
        simpa only [wE] using hEUnramified
      have hsigmaR : sigmaR = 1 :=
        hphi.isUnramified_mk_iff.mp
          (hmk.symm ▸ hEUnramified)
      apply MonoidHom.ext
      intro x
      unfold infinitePlaceArtinMonoidHomOfPlace
      rw [dite_eq_right hLUnramified, dite_eq_left hEUnramified']
      simp only [MonoidHom.comp_apply]
      dsimp
      split_ifs with hsign
      · simp
      · simpa [sigmaR, sigmaL] using hsigmaR
    · have hEUnramified' :
          ¬ (wL.comap (algebraMap E L)).IsUnramified K := by
        simpa only [wE] using hEUnramified
      have hERamified : wE.IsRamified K :=
        hEUnramified
      let sigmaE :=
        ramifiedInfinitePlaceConjugation
          (K := K) wE hERamified
      have hsigmaE :=
        ramifiedInfinitePlaceConjugation_isConj
          (K := K) wE hERamified
      have hsigmaRNe : sigmaR ≠ 1 := by
        intro hsigmaR
        have :
            (InfinitePlace.mk phi).IsUnramified K :=
          hphi.isUnramified_mk_iff.mpr hsigmaR
        exact hEUnramified (hmk ▸ this)
      have hsigmaRMem :
          sigmaR ∈
            MulAction.stabilizer (E ≃ₐ[K] E) wE := by
        rw [← hmk,
          InfinitePlace.mem_stabilizer_mk_iff]
        exact Or.inr hphi
      have hsigmaRAtWE :
          NumberField.ComplexEmbedding.IsConj
            (InfinitePlace.embedding wE) sigmaR := by
        rw [← InfinitePlace.mk_embedding wE,
          InfinitePlace.mem_stabilizer_mk_iff] at hsigmaRMem
        exact hsigmaRMem.resolve_left hsigmaRNe
      have hsigmaREq : sigmaR = sigmaE :=
        hsigmaRAtWE.ext hsigmaE
      apply MonoidHom.ext
      intro x
      unfold infinitePlaceArtinMonoidHomOfPlace
      rw [dite_eq_right hLUnramified, dite_eq_right hEUnramified']
      simp only [MonoidHom.comp_apply]
      dsimp
      split_ifs with hsign
      · simp
      · simpa [sigmaR, sigmaL, sigmaE] using hsigmaREq

open scoped Classical in
/-- The norm from a complex archimedean completion to a real completion
is positive under the canonical real coordinate. -/
theorem infinitePlace_normUnits_real_complex_pos
    {K' : Type}
    [Field K'] [NumberField K'] [Algebra K K']
    (v : InfinitePlace K) (W : InfinitePlace K')
    (hW : W.comap (algebraMap K K') = v)
    (hvReal : v.IsReal) (hWComplex : W.IsComplex)
    (x : W.Completionˣ) :
    letI : W.1.LiesOver v.1 :=
      ⟨congrArg (fun q : InfinitePlace K => q.1) hW⟩
    0 <
      InfinitePlace.Completion.ringEquivRealOfIsReal
        hvReal
        (LocalFieldTheory.normUnits
          v.Completion W.Completion x :
            v.Completion) := by
  let : W.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) hW⟩
  let eReal :
      v.Completion ≃+* ℝ :=
    InfinitePlace.Completion.ringEquivRealOfIsReal
      hvReal
  let eComplex :
      W.Completion ≃+* ℂ :=
    InfinitePlace.Completion.ringEquivComplexOfIsComplex
      hWComplex
  let :
      NumberField.ComplexEmbedding.LiesOver
        (InfinitePlace.Completion.extensionEmbedding W)
        (InfinitePlace.Completion.extensionEmbedding v) :=
    InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal
      W hvReal
  have hCompatible :
      RingHom.comp (algebraMap ℝ ℂ) eReal =
        RingHom.comp eComplex
          (algebraMap v.Completion W.Completion) := by
    ext z
    simp [eReal, eComplex]
  have hNorm :=
    LocalClassFieldTheory.normUnits_map_ringEquiv
      eReal eComplex hCompatible x
  have hNormVal := congrArg Units.val hNorm
  change
    0 <
      ((Units.mapEquiv eReal.toMulEquiv
        (LocalFieldTheory.normUnits
          v.Completion W.Completion x) : ℝˣ) : ℝ)
  rw [hNormVal]
  change
    0 <
      Algebra.norm ℝ
        (eComplex (x : W.Completion))
  rw [Algebra.norm_complex_apply, Complex.normSq_pos]
  exact (map_ne_zero eComplex).2 (Units.ne_zero x)

open scoped Classical in
/-- The norm between real archimedean completions agrees with the
transported local unit under their canonical real coordinates. -/
theorem infinitePlace_normUnits_real_real
    {K' : Type}
    [Field K'] [NumberField K'] [Algebra K K']
    (v : InfinitePlace K) (W : InfinitePlace K')
    (hW : W.comap (algebraMap K K') = v)
    (hvReal : v.IsReal) (hWReal : W.IsReal)
    (x : W.Completionˣ) :
    letI : W.1.LiesOver v.1 :=
      ⟨congrArg (fun q : InfinitePlace K => q.1) hW⟩
    Units.mapEquiv
        (InfinitePlace.Completion.ringEquivRealOfIsReal
          hvReal).toMulEquiv
        (LocalFieldTheory.normUnits
          v.Completion W.Completion x) =
      Units.mapEquiv
        (InfinitePlace.Completion.ringEquivRealOfIsReal
          hWReal).toMulEquiv x := by
  let : W.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) hW⟩
  let eBase :
      v.Completion ≃+* ℝ :=
    InfinitePlace.Completion.ringEquivRealOfIsReal
      hvReal
  let eExtension :
      W.Completion ≃+* ℝ :=
    InfinitePlace.Completion.ringEquivRealOfIsReal
      hWReal
  let :
      NumberField.ComplexEmbedding.LiesOver
        (InfinitePlace.Completion.extensionEmbedding W)
        (InfinitePlace.Completion.extensionEmbedding v) :=
    InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal
      W hvReal
  have hCompatible :
      RingHom.comp (algebraMap ℝ ℝ) eBase =
        RingHom.comp eExtension
          (algebraMap v.Completion W.Completion) := by
    ext z
    change
      InfinitePlace.Completion.extensionEmbeddingOfIsReal
          hvReal z =
        InfinitePlace.Completion.extensionEmbeddingOfIsReal
          hWReal ((algebraMap v.Completion W.Completion) z)
    apply Complex.ofReal_injective
    simpa only [
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply] using
      (InfinitePlace.Completion.liesOver_extensionEmbedding_apply
        W (v := v)).symm
  simpa only [
    LocalFieldTheory.normUnits,
    Algebra.norm_self,
    Units.map_id,
    MonoidHom.id_apply
  ] using
    LocalClassFieldTheory.normUnits_map_ringEquiv
      eBase eExtension hCompatible x

omit [NumberField K] [NumberField L] in
/-- Complex conjugation restricts along a compatible tower of field embeddings. -/
private theorem complexEmbedding_isConj_restriction
    {K' L' : Type} [Field K'] [Field L']
    [Algebra K K'] [Algebra K' L'] [Algebra K L'] [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    (σ : L' ≃ₐ[K'] L') (φ : L' →+* ℂ)
    (hφ : NumberField.ComplexEmbedding.IsConj φ σ) :
    NumberField.ComplexEmbedding.IsConj (φ.comp (algebraMap L L'))
      (((AlgEquiv.restrictNormalHom L).comp (AlgEquiv.restrictScalarsHom K)) σ) := by
  apply RingHom.ext
  intro x
  change star (φ (algebraMap L L' x)) =
    φ (algebraMap L L' ((AlgEquiv.restrictNormal (AlgEquiv.restrictScalars K σ) L) x))
  rw [AlgEquiv.restrictNormal_commutes]
  exact (hφ.eq (algebraMap L L' x)).symm

omit [NumberField L] in
open scoped Classical in
/-- The archimedean Artin map attached to specified places carries a
local norm to the restriction of the upper Artin element. -/
theorem infinitePlaceArtinMonoidHomOfPlace_norm_restriction
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L']
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L']
    (v : InfinitePlace K) (W : InfinitePlace K')
    (w' : InfinitePlace L')
    (hW : W.comap (algebraMap K K') = v)
    (hw' : w'.comap (algebraMap K' L') = W) :
    let w := w'.comap (algebraMap L L')
    let hw : w.comap (algebraMap K L) = v := by
      dsimp only [w]
      rw [← InfinitePlace.comap_comp,
        ← IsScalarTower.algebraMap_eq K L L',
        IsScalarTower.algebraMap_eq K K' L',
        InfinitePlace.comap_comp, hw', hW]
    letI : W.1.LiesOver v.1 :=
      ⟨congrArg (fun q : InfinitePlace K => q.1) hW⟩
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (infinitePlaceArtinMonoidHomOfPlace
          (K := K') (L := L') W w' hw') =
      (infinitePlaceArtinMonoidHomOfPlace
        (K := K) (L := L) v w hw).comp
        (LocalFieldTheory.normUnits
          v.Completion W.Completion) := by
  let w := w'.comap (algebraMap L L')
  have hw :
      w.comap (algebraMap K L) = v := by
    dsimp only [w]
    rw [← InfinitePlace.comap_comp,
      ← IsScalarTower.algebraMap_eq K L L',
      IsScalarTower.algebraMap_eq K K' L',
      InfinitePlace.comap_comp, hw', hW]
  let : W.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) hW⟩
  dsimp only
  by_cases hUpperUnramified : w'.IsUnramified K'
  · by_cases hLowerUnramified : w.IsUnramified K
    · have hLowerUnramified' :
          (w'.comap (algebraMap L L')).IsUnramified K := by
        simpa only [w] using hLowerUnramified
      unfold infinitePlaceArtinMonoidHomOfPlace
      rw [dite_eq_left hUpperUnramified, dite_eq_left hLowerUnramified']
      simp
    · have hLowerUnramified' :
          ¬ (w'.comap (algebraMap L L')).IsUnramified K := by
        simpa only [w] using hLowerUnramified
      have hLowerRamified : w.IsRamified K :=
        hLowerUnramified
      have hvReal : v.IsReal := by
        rw [← hw]
        exact hLowerRamified.isReal
      have hw'Complex : w'.IsComplex := by
        rw [← InfinitePlace.not_isReal_iff_isComplex]
        intro hw'Real
        have hwReal : w.IsReal := by
          exact hw'Real.comap (algebraMap L L')
        exact
          (InfinitePlace.not_isComplex_iff_isReal.mpr
            hwReal) hLowerRamified.isComplex
      have hWComplex : W.IsComplex := by
        rcases
            InfinitePlace.isUnramified_iff.mp
              hUpperUnramified with
          hw'Real | hWComplex
        · exact
            (InfinitePlace.not_isReal_iff_isComplex.mpr
              hw'Complex hw'Real).elim
        · simpa only [hw'] using hWComplex
      apply MonoidHom.ext
      intro x
      have hPositive :=
        infinitePlace_normUnits_real_complex_pos
          (K := K) v W hW hvReal hWComplex x
      have hSign :
          LocalClassFieldTheory.realUnitsSign
              (Units.mapEquiv
                (InfinitePlace.Completion.ringEquivRealOfIsReal
                  hvReal).toMulEquiv
                (LocalFieldTheory.normUnits
                  v.Completion W.Completion x)) =
            1 :=
        MonoidHom.mem_ker.mp
          ((LocalClassFieldTheory.mem_realUnitsSign_ker_iff _).2
            hPositive)
      unfold infinitePlaceArtinMonoidHomOfPlace
      rw [dite_eq_left hUpperUnramified, dite_eq_right hLowerUnramified']
      simp only [MonoidHom.comp_apply]
      dsimp
      split_ifs with hsign
      · exact map_one _
      · exact (hsign hSign).elim
  · have hUpperRamified : w'.IsRamified K' :=
      hUpperUnramified
    have hWReal : W.IsReal := by
      rw [← hw']
      exact hUpperRamified.isReal
    have hvReal : v.IsReal := by
      rw [← hW]
      exact hWReal.comap (algebraMap K K')
    let sigmaUpper :=
      ramifiedInfinitePlaceConjugation
        (K := K') w' hUpperRamified
    let sigmaRestricted : L ≃ₐ[K] L :=
      ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)) sigmaUpper
    have hSigmaUpper :=
      ramifiedInfinitePlaceConjugation_isConj
        (K := K') w' hUpperRamified
    let phi : L →+* ℂ :=
      (InfinitePlace.embedding w').comp
        (algebraMap L L')
    have hphi : NumberField.ComplexEmbedding.IsConj phi sigmaRestricted :=
      complexEmbedding_isConj_restriction sigmaUpper (InfinitePlace.embedding w') hSigmaUpper
    have hmk : InfinitePlace.mk phi = w := by
      change
        InfinitePlace.mk
            ((InfinitePlace.embedding w').comp
              (algebraMap L L')) =
          w'.comap (algebraMap L L')
      conv_rhs => rw [← InfinitePlace.mk_embedding w']
      rw [InfinitePlace.comap_mk]
    have hSign (x : W.Completionˣ) :
        LocalClassFieldTheory.realUnitsSign
            (Units.mapEquiv
              (InfinitePlace.Completion.ringEquivRealOfIsReal
                hWReal).toMulEquiv x) =
          LocalClassFieldTheory.realUnitsSign
            (Units.mapEquiv
              (InfinitePlace.Completion.ringEquivRealOfIsReal
                hvReal).toMulEquiv
              (LocalFieldTheory.normUnits
                v.Completion W.Completion x)) := by
      rw [infinitePlace_normUnits_real_real
        (K := K) v W hW hvReal hWReal x]
    by_cases hLowerUnramified : w.IsUnramified K
    · have hLowerUnramified' :
          (w'.comap (algebraMap L L')).IsUnramified K := by
        simpa only [w] using hLowerUnramified
      have hSigmaRestricted : sigmaRestricted = 1 :=
        hphi.isUnramified_mk_iff.mp
          (hmk.symm ▸ hLowerUnramified)
      apply MonoidHom.ext
      intro x
      unfold infinitePlaceArtinMonoidHomOfPlace
      rw [dite_eq_right hUpperUnramified, dite_eq_left hLowerUnramified']
      simp only [MonoidHom.comp_apply]
      dsimp
      split_ifs with hsign
      · change
          ((AlgEquiv.restrictNormalHom L).comp
            (AlgEquiv.restrictScalarsHom K)) 1 =
            1
        exact map_one _
      · simpa [sigmaRestricted, sigmaUpper] using hSigmaRestricted
    · have hLowerUnramified' :
          ¬ (w'.comap (algebraMap L L')).IsUnramified K := by
        simpa only [w] using hLowerUnramified
      have hLowerRamified : w.IsRamified K :=
        hLowerUnramified
      let sigmaLower :=
        ramifiedInfinitePlaceConjugation
          (K := K) w hLowerRamified
      have hSigmaLower :=
        ramifiedInfinitePlaceConjugation_isConj
          (K := K) w hLowerRamified
      have hSigmaRestrictedNe :
          sigmaRestricted ≠ 1 := by
        intro hSigmaRestricted
        have :
            (InfinitePlace.mk phi).IsUnramified K :=
          hphi.isUnramified_mk_iff.mpr
            hSigmaRestricted
        exact hLowerUnramified (hmk ▸ this)
      have hSigmaRestrictedMem :
          sigmaRestricted ∈
            MulAction.stabilizer
              (L ≃ₐ[K] L) w := by
        rw [← hmk,
          InfinitePlace.mem_stabilizer_mk_iff]
        exact Or.inr hphi
      have hSigmaRestrictedAtW :
          NumberField.ComplexEmbedding.IsConj
            (InfinitePlace.embedding w)
            sigmaRestricted := by
        rw [← InfinitePlace.mk_embedding w,
          InfinitePlace.mem_stabilizer_mk_iff] at hSigmaRestrictedMem
        exact
          hSigmaRestrictedMem.resolve_left
            hSigmaRestrictedNe
      have hSigmaEq :
          sigmaRestricted = sigmaLower :=
        hSigmaRestrictedAtW.ext hSigmaLower
      apply MonoidHom.ext
      intro x
      unfold infinitePlaceArtinMonoidHomOfPlace
      rw [dite_eq_right hUpperUnramified, dite_eq_right hLowerUnramified']
      simp only [MonoidHom.comp_apply]
      dsimp
      split_ifs with hsignUpper hsignLower hsignLower
      · exact map_one _
      · exact (hsignLower ((hSign x).symm.trans hsignUpper)).elim
      · exact (hsignUpper ((hSign x).trans hsignLower)).elim
      · simpa [sigmaRestricted, sigmaUpper, sigmaLower] using hSigmaEq

omit [NumberField K] [NumberField L] in
open scoped Classical in
/-- Archimedean local factors commute with restriction in an abelian
number-field tower. -/
theorem chosenInfinitePlaceArtinMonoidHom_restrict_tower
    {E : Type}
    [Field E] [NumberField E]
    [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    [IsAbelianGalois K E]
    (v : InfinitePlace K) :
    (AlgEquiv.restrictNormalHom E).comp
        (chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v) =
      chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := E) v := by
  let wL :=
    chosenInfinitePlaceAbove
      (L := L) v
  let wE := wL.comap (algebraMap E L)
  have hwL :
      wL.comap (algebraMap K L) = v :=
    chosenInfinitePlaceAbove_comap
      (L := L) v
  have hwE :
      wE.comap (algebraMap K E) = v := by
    dsimp only [wE]
    rw [← InfinitePlace.comap_comp,
      ← IsScalarTower.algebraMap_eq K E L, hwL]
  calc
    (AlgEquiv.restrictNormalHom E).comp
        (chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v) =
      infinitePlaceArtinMonoidHomOfPlace
        (K := K) (L := E) v wE hwE :=
      infinitePlaceArtinMonoidHomOfPlace_restrict_tower
        (K := K) (L := L) (E := E)
        v wL hwL hwE
    _ = chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := E) v :=
      infinitePlaceArtinMonoidHomOfPlace_eq
        (K := K) (L := E) v wE
        (chosenInfinitePlaceAbove
          (L := E) v)
        hwE
        (chosenInfinitePlaceAbove_comap
          (L := E) v)

omit [NumberField L] in
open scoped Classical in
/-- In an actual number-field diamond `K ⊂ K'`, `L ⊂ L'`, the
archimedean local Artin factor commutes with the ordinary completion
norm and with the standard restriction composite supplied by mathlib. -/
theorem chosenInfinitePlaceArtinMonoidHom_norm_restriction
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L']
    (W : InfinitePlace K') :
    let v := infinitePlaceBelow (K := K) W
    letI : W.1.LiesOver v.1 := ⟨rfl⟩
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (chosenInfinitePlaceArtinMonoidHom
          (K := K') (L := L') W) =
      (chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v).comp
        (LocalFieldTheory.normUnits
          v.Completion W.Completion) := by
  let v := infinitePlaceBelow (K := K) W
  let w' :=
    chosenInfinitePlaceAbove
      (L := L') W
  let w := w'.comap (algebraMap L L')
  have hW :
      W.comap (algebraMap K K') = v := rfl
  have hw' :
      w'.comap (algebraMap K' L') = W :=
    chosenInfinitePlaceAbove_comap
      (L := L') W
  have hw :
      w.comap (algebraMap K L) = v := by
    dsimp only [w]
    rw [← InfinitePlace.comap_comp,
      ← IsScalarTower.algebraMap_eq K L L',
      IsScalarTower.algebraMap_eq K K' L',
      InfinitePlace.comap_comp, hw', hW]
  let : W.1.LiesOver v.1 := ⟨rfl⟩
  calc
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (chosenInfinitePlaceArtinMonoidHom
          (K := K') (L := L') W) =
      (infinitePlaceArtinMonoidHomOfPlace
        (K := K) (L := L) v w hw).comp
          (LocalFieldTheory.normUnits
            v.Completion W.Completion) :=
      infinitePlaceArtinMonoidHomOfPlace_norm_restriction
        (K := K) (L := L) v W w' hW hw'
    _ =
      (chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v).comp
          (LocalFieldTheory.normUnits
            v.Completion W.Completion) := by
      rw [chosenInfinitePlaceArtinMonoidHom]
      rw [infinitePlaceArtinMonoidHomOfPlace_eq
        (K := K) (L := L) v w
        (chosenInfinitePlaceAbove
          (L := L) v)
        hw
        (chosenInfinitePlaceAbove_comap
          (L := L) v)]

end AbelianTower

section Galois

variable [IsGalois K L]

omit [NumberField K] [NumberField L] in
open scoped Classical in
/-- The chosen archimedean Artin homomorphism is continuous. -/
theorem chosenInfinitePlaceArtinMonoidHom_continuous
    (v : InfinitePlace K) :
    Continuous
      (chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v) := by
  classical
  let w :=
    chosenInfinitePlaceAbove
      (L := L) v
  by_cases hUnramified : w.IsUnramified K
  · have hUnramified' :
        (chosenInfinitePlaceAbove (L := L) v).IsUnramified K := by
      simpa only [w] using hUnramified
    unfold chosenInfinitePlaceArtinMonoidHom
    unfold infinitePlaceArtinMonoidHomOfPlace
    rw [dite_eq_left hUnramified']
    exact continuous_const
  · have hUnramified' :
        ¬ (chosenInfinitePlaceAbove (L := L) v).IsUnramified K := by
      simpa only [w] using hUnramified
    have hRamified : w.IsRamified K := hUnramified
    have hvReal : v.IsReal := by
      rw [← chosenInfinitePlaceAbove_comap (L := L) v]
      exact hRamified.isReal
    let e : v.Completionˣ ≃ₜ* ℝˣ :=
      Units.mapContinuousMulEquiv
        (RayClass.realCompletionContinuousMulEquiv v hvReal)
    let signToGalois : ℤˣ → (L ≃ₐ[K] L) :=
      fun u =>
        if u = 1 then 1
        else
          ramifiedInfinitePlaceConjugation
            (K := K)
            (chosenInfinitePlaceAbove (L := L) v)
            hUnramified'
    have hSignToGalois : Continuous signToGalois :=
      continuous_of_discreteTopology
    have hMap :
        Continuous fun x : v.Completionˣ =>
          Units.mapEquiv
            (InfinitePlace.Completion.ringEquivRealOfIsReal
              hvReal).toMulEquiv x := by
      change Continuous e
      exact e.continuous_toFun
    unfold chosenInfinitePlaceArtinMonoidHom
    unfold infinitePlaceArtinMonoidHomOfPlace
    rw [dite_eq_right hUnramified']
    change
      Continuous fun x : v.Completionˣ =>
        signToGalois
          (LocalClassFieldTheory.realUnitsSign
            (Units.mapEquiv
              (InfinitePlace.Completion.ringEquivRealOfIsReal
                hvReal).toMulEquiv x))
    exact hSignToGalois.comp
      (LocalClassFieldTheory.realUnitsSign_continuous.comp hMap)

omit [NumberField K] [NumberField L] in
open scoped Classical in
/-- A positive element at a real place has trivial archimedean Artin
symbol. -/
theorem chosenInfinitePlaceArtinMonoidHom_eq_one_of_real_pos
    (v : InfinitePlace K) (hvReal : v.IsReal)
    (x : v.Completionˣ)
    (hx :
      0 <
        InfinitePlace.Completion.ringEquivRealOfIsReal
          hvReal (x : v.Completion)) :
    chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v x = 1 := by
  let e : v.Completion ≃+* ℝ :=
    InfinitePlace.Completion.ringEquivRealOfIsReal
      hvReal
  let eu : v.Completionˣ ≃* ℝˣ :=
    Units.mapEquiv e.toMulEquiv
  have hx' : 0 < (eu x : ℝ) := by
    simpa [eu, e] using hx
  have hsign :
      LocalClassFieldTheory.realUnitsSign (eu x) = 1 :=
    MonoidHom.mem_ker.mp
      ((LocalClassFieldTheory.mem_realUnitsSign_ker_iff
        (eu x)).2 hx')
  have hsign' :
      LocalClassFieldTheory.realUnitsSign
          (Units.mapEquiv
            (InfinitePlace.Completion.ringEquivRealOfIsReal
              hvReal).toMulEquiv x) = 1 := by
    simpa [eu, e] using hsign
  let w :=
    chosenInfinitePlaceAbove
      (L := L) v
  by_cases hUnramified : w.IsUnramified K
  · have hUnramified' :
        (chosenInfinitePlaceAbove (L := L) v).IsUnramified K := by
      simpa only [w] using hUnramified
    unfold chosenInfinitePlaceArtinMonoidHom
    unfold infinitePlaceArtinMonoidHomOfPlace
    rw [dite_eq_left hUnramified']
    rfl
  · have hUnramified' :
        ¬ (chosenInfinitePlaceAbove (L := L) v).IsUnramified K := by
      simpa only [w] using hUnramified
    unfold chosenInfinitePlaceArtinMonoidHom
    unfold infinitePlaceArtinMonoidHomOfPlace
    rw [dite_eq_right hUnramified']
    simp only [MonoidHom.comp_apply]
    change
      (if
          LocalClassFieldTheory.realUnitsSign
              (Units.mapEquiv
                (InfinitePlace.Completion.ringEquivRealOfIsReal
                  hvReal).toMulEquiv x) =
            1 then
        1
      else _) =
        1
    rw [hsign']
    simp

universe uNorm vNorm

/-- Compatible changes of both fields carry the local norm subgroup to the new norm subgroup. -/
private theorem localNormSubgroup_map_ringEquivs
    {F E : Type uNorm} {F' E' : Type vNorm}
    [Field F] [Field E] [Field F'] [Field E']
    [Algebra F E] [Algebra F' E'] (eBase : F ≃+* F') (eExtension : E ≃+* E')
    (hCompatible : (algebraMap F' E').comp eBase.toRingHom =
      eExtension.toRingHom.comp (algebraMap F E)) :
    (localNormSubgroup F E).map (Units.mapEquiv eBase.toMulEquiv).toMonoidHom =
      localNormSubgroup F' E' := by
  let eExtensionUnits := Units.mapEquiv eExtension.toMulEquiv
  ext x
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨eExtensionUnits y,
      (LocalClassFieldTheory.normUnits_map_ringEquiv eBase eExtension hCompatible y).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨normUnits F E (eExtensionUnits.symm y), ⟨_, rfl⟩, ?_⟩
    change Units.mapEquiv eBase.toMulEquiv (normUnits F E (eExtensionUnits.symm y)) = _
    rw [LocalClassFieldTheory.normUnits_map_ringEquiv eBase eExtension hCompatible]
    exact congrArg (normUnits F' E') (eExtensionUnits.apply_symm_apply y)

open scoped Classical in
/-- The kernel of the actual Artin homomorphism at an infinite place
is exactly the determinant-norm image on the corresponding tensor
factor. -/
theorem chosenInfinitePlaceArtinMonoidHom_ker
    (v : InfinitePlace K) :
    MonoidHom.ker
        (chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v) =
      infiniteTensorNormSubgroup
        (K := K) (L := L) v := by
  let w :=
    chosenInfinitePlaceAbove
      (L := L) v
  have hw :
      w.comap (algebraMap K L) = v :=
    chosenInfinitePlaceAbove_comap
      (L := L) v
  let : w.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
  rw [
    infiniteTensorNormSubgroup_eq_localNormSubgroup
      (K := K) (L := L) v w hw]
  by_cases hUnramified : w.IsUnramified K
  · have hDegree :
        Module.finrank v.Completion w.Completion = 1 :=
      InfinitePlace.IsUnramified.finrank_eq_one v hUnramified
    have hNormTop :
        localNormSubgroup
          v.Completion w.Completion = ⊤ := by
      apply top_unique
      intro x _
      refine
        ⟨Units.map
            (algebraMap
              v.Completion w.Completion).toMonoidHom x,
          ?_⟩
      apply Units.ext
      change
        Algebra.norm v.Completion
            (algebraMap v.Completion w.Completion
              (x : v.Completion)) =
          (x : v.Completion)
      rw [Algebra.norm_algebraMap, hDegree, pow_one]
    rw [hNormTop, MonoidHom.ker_eq_top_iff]
    have hUnramified' :
        (chosenInfinitePlaceAbove (L := L) v).IsUnramified K := by
      simpa only [w] using hUnramified
    unfold chosenInfinitePlaceArtinMonoidHom
    unfold infinitePlaceArtinMonoidHomOfPlace
    rw [dite_eq_left hUnramified']
  · have hRamified : w.IsRamified K :=
      hUnramified
    have hvReal : v.IsReal := by
      rw [← hw]
      exact hRamified.isReal
    let σ :=
      ramifiedInfinitePlaceConjugation
        (K := K) w hRamified
    have hσ :=
      ramifiedInfinitePlaceConjugation_isConj
        (K := K) w hRamified
    have hσsq : σ * σ = 1 := by
      exact
        ramifiedInfinitePlaceConjugation_sq
          (K := K) w hRamified
    let signToGalois : ℤˣ →* (L ≃ₐ[K] L) :=
      { toFun := fun u =>
          if u = 1 then 1 else σ
        map_one' := ite_eq_left rfl
        map_mul' := by
          intro x y
          rcases Int.units_eq_one_or x with rfl | rfl
          · simp
          rcases Int.units_eq_one_or y with rfl | rfl
          · simp
          · simp [hσsq] }
    have hσne : σ ≠ 1 :=
      (NumberField.ComplexEmbedding.isConj_ne_one_iff
        hσ).2
        (InfinitePlace.isComplex_iff.mp
          hRamified.isComplex)
    have hSignInjective :
        Function.Injective signToGalois := by
      intro x y hxy
      rcases Int.units_eq_one_or x with rfl | rfl
      · rcases Int.units_eq_one_or y with rfl | rfl
        · rfl
        · exfalso
          apply hσne
          simpa [signToGalois] using
            hxy.symm
      · rcases Int.units_eq_one_or y with rfl | rfl
        · exfalso
          apply hσne
          simpa [signToGalois] using
            hxy
        · rfl
    let eRealField :
        v.Completion ≃+* ℝ :=
      InfinitePlace.Completion.ringEquivRealOfIsReal
        hvReal
    let completionUnitsEquivRealUnits :
        v.Completionˣ ≃* ℝˣ :=
      Units.mapEquiv eRealField.toMulEquiv
    have hwComplex : w.IsComplex :=
      hRamified.isComplex
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
      simp [eRealField, eComplexField]
    have hCompletionCompatibleSymm :=
      LocalClassFieldTheory.ringEquiv_compat_symm
        eRealField eComplexField hCompletionCompatible
    have hRealComplexNormTransport :
        (localNormSubgroup ℝ ℂ).map completionUnitsEquivRealUnits.symm.toMonoidHom =
          localNormSubgroup v.Completion w.Completion :=
      localNormSubgroup_map_ringEquivs eRealField.symm eComplexField.symm
        hCompletionCompatibleSymm
    simp only [chosenInfinitePlaceArtinMonoidHom,
      infinitePlaceArtinMonoidHomOfPlace,
      w, hUnramified]
    change
      MonoidHom.ker
          (signToGalois.comp
            (LocalClassFieldTheory.realUnitsSign.comp
              completionUnitsEquivRealUnits.toMonoidHom)) =
        localNormSubgroup
          v.Completion w.Completion
    calc
      MonoidHom.ker
          (signToGalois.comp
            (LocalClassFieldTheory.realUnitsSign.comp
              completionUnitsEquivRealUnits.toMonoidHom)) =
          MonoidHom.ker
            (LocalClassFieldTheory.realUnitsSign.comp
              completionUnitsEquivRealUnits.toMonoidHom) :=
        MonoidHom.ker_comp_of_injective _ _ hSignInjective
      _ =
          Subgroup.map completionUnitsEquivRealUnits.symm.toMonoidHom
            (MonoidHom.ker LocalClassFieldTheory.realUnitsSign) :=
        MonoidHom.ker_comp_mulEquiv
          LocalClassFieldTheory.realUnitsSign
          completionUnitsEquivRealUnits
      _ =
          Subgroup.map completionUnitsEquivRealUnits.symm.toMonoidHom
            (localNormSubgroup ℝ ℂ) := by
        rw [LocalClassFieldTheory.realUnitsSign_ker_eq_complexNormSubgroup]
      _ = localNormSubgroup v.Completion w.Completion :=
        hRealComplexNormTransport

end Galois

variable [IsAbelianGalois K L]

open scoped Classical in
/-- The product of the actual archimedean local Artin homomorphisms
over the finite set of infinite places of `K`. -/
noncomputable def infinitePlaceGlobalArtinMonoidHom :
    IdeleGroup K →* (L ≃ₐ[K] L) :=
  ∏ v : InfinitePlace K,
    (chosenInfinitePlaceArtinMonoidHom
      (K := K) (L := L) v).comp
      (IdeleGroup.infiniteComponent v)

omit [NumberField L] in
open scoped Classical in
/-- The archimedean global Artin product is continuous. -/
theorem infinitePlaceGlobalArtinMonoidHom_continuous :
    Continuous
      (infinitePlaceGlobalArtinMonoidHom
        (K := K) (L := L)) := by
  unfold infinitePlaceGlobalArtinMonoidHom
  rw [MonoidHom.coe_finsetProd]
  have hprod :
      (∏ v : InfinitePlace K,
        ⇑((chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v).comp
          (IdeleGroup.infiniteComponent v))) =
        fun a : IdeleGroup K =>
          ∏ v : InfinitePlace K,
            chosenInfinitePlaceArtinMonoidHom
              (K := K) (L := L) v
              (IdeleGroup.infiniteComponent v a) := by
    funext a
    simp only [Finset.prod_apply, MonoidHom.comp_apply]
  rw [hprod]
  apply continuous_finsetProd Finset.univ
  intro v _
  exact
    (chosenInfinitePlaceArtinMonoidHom_continuous
      (K := K) (L := L) v).comp
        (IdeleGroup.infiniteComponentContinuous v).continuous

omit [NumberField L] in
open scoped Classical in
/-- The archimedean Artin product after an idele norm is the product,
over all infinite places upstairs, of the base local Artin maps applied
to the corresponding local field norms. -/
theorem infinitePlaceGlobalArtinMonoidHom_norm_eq_prod
    {M : Type}
    [Field M] [NumberField M] [Algebra K M]
    (a : IdeleGroup M) :
    letI : ∀ W : InfinitePlace M,
        W.1.LiesOver
          (infinitePlaceBelow (K := K) W).1 :=
      fun _ => ⟨rfl⟩
    infinitePlaceGlobalArtinMonoidHom
        (K := K) (L := L)
        (IdeleGroup.norm K M a) =
      ∏ W : InfinitePlace M,
        chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L)
          (infinitePlaceBelow (K := K) W)
          (LocalFieldTheory.normUnits
            (infinitePlaceBelow
              (K := K) W).Completion
            W.Completion
            (IdeleGroup.infiniteComponent W a)) := by
  classical
  let : ∀ W : InfinitePlace M,
      W.1.LiesOver
        (infinitePlaceBelow (K := K) W).1 :=
    fun _ => ⟨rfl⟩
  let factor : InfinitePlace M → (L ≃ₐ[K] L) :=
    fun W =>
      chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L)
        (infinitePlaceBelow (K := K) W)
        (LocalFieldTheory.normUnits
          (infinitePlaceBelow
            (K := K) W).Completion
          W.Completion
          (IdeleGroup.infiniteComponent W a))
  unfold infinitePlaceGlobalArtinMonoidHom
  rw [MonoidHom.finsetProd_apply]
  change
    (∏ v : InfinitePlace K,
      chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v
        (IdeleGroup.infiniteComponent v
          (IdeleGroup.norm K M a))) =
      ∏ W : InfinitePlace M, factor W
  calc
    (∏ v : InfinitePlace K,
        chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (IdeleGroup.infiniteComponent v
            (IdeleGroup.norm K M a))) =
        ∏ v : InfinitePlace K,
          ∏ W ∈ Finset.univ with
              infinitePlaceBelow (K := K) W = v,
            factor W := by
      apply Finset.prod_congr rfl
      intro v _
      let vK := v.1
      let hvK : vK.IsNontrivial := v.isNontrivial
      let eAbove :=
        infinitePlaceAboveEquivExtension
          (K := K) (L := M) v
      let :=
        AlgebraicNumberTheory.Valuations.completionTensorDecompositionExtensionFintype
          (K := K) (L := M) vK hvK
      let : Fintype {W : InfinitePlace M //
          infinitePlaceBelow (K := K) W = v} :=
        Fintype.ofEquiv
          (AlgebraicNumberTheory.Valuations.AbsoluteValueExtension vK M)
          eAbove.symm
      let : ∀ W : {W : InfinitePlace M //
          infinitePlaceBelow (K := K) W = v},
          W.1.1.LiesOver v.1 :=
        fun W =>
          ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
      rw [IdeleGroup.infiniteComponent_norm_eq_prod]
      rw [map_prod]
      symm
      rw [Finset.prod_subtype
        (p := fun W : InfinitePlace M =>
          infinitePlaceBelow (K := K) W = v)
        (s := Finset.univ.filter fun W : InfinitePlace M =>
          infinitePlaceBelow (K := K) W = v)
        (by intro W; simp)]
      apply Finset.prod_congr rfl
      intro W _
      rcases W with ⟨W, rfl⟩
      rfl
    _ = ∏ W : InfinitePlace M, factor W :=
      Finset.prod_fiberwise
        Finset.univ
        (infinitePlaceBelow (K := K))
        factor

omit [NumberField L] in
open scoped Classical in
/-- The archimedean part of the Artin norm--restriction field diamond.
Restriction of the upper infinite Artin product is the lower infinite Artin
product after the ordinary idele norm. -/
theorem infinitePlaceGlobalArtinMonoidHom_norm_restriction
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L'] :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (infinitePlaceGlobalArtinMonoidHom
          (K := K') (L := L')) =
      (infinitePlaceGlobalArtinMonoidHom
        (K := K) (L := L)).comp
        (IdeleGroup.norm K K') := by
  apply MonoidHom.ext
  intro a
  let : ∀ W : InfinitePlace K',
      W.1.LiesOver
        (infinitePlaceBelow
          (K := K) W).1 :=
    fun _ => ⟨rfl⟩
  change
    ((AlgEquiv.restrictNormalHom L).comp
      (AlgEquiv.restrictScalarsHom K))
      (infinitePlaceGlobalArtinMonoidHom
        (K := K') (L := L') a) =
      infinitePlaceGlobalArtinMonoidHom
        (K := K) (L := L)
        (IdeleGroup.norm K K' a)
  rw [infinitePlaceGlobalArtinMonoidHom_norm_eq_prod]
  unfold infinitePlaceGlobalArtinMonoidHom
  rw [MonoidHom.finsetProd_apply]
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro W _
  exact
    DFunLike.congr_fun
      (chosenInfinitePlaceArtinMonoidHom_norm_restriction
        (K := K) (L := L) W)
      (IdeleGroup.infiniteComponent W a)

omit [NumberField L] in
open scoped Classical in
/-- Every archimedean factor is trivial on a finite one-place idele. -/
@[simp]
theorem infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    infinitePlaceGlobalArtinMonoidHom
        (K := K) (L := L)
        (finitePlaceIdele v x) =
  1 := by
  unfold infinitePlaceGlobalArtinMonoidHom
  rw [MonoidHom.finsetProd_apply]
  apply Finset.prod_eq_one
  intro w _
  change
    chosenInfinitePlaceArtinMonoidHom
      (K := K) (L := L) w
      (IdeleGroup.infiniteComponent w
        (finitePlaceIdele v x)) =
      1
  have hcomponent :
      IdeleGroup.infiniteComponent w
          (finitePlaceIdele v x) =
        (1 : w.Completionˣ) :=
    finitePlaceIdele_infiniteComponent v w x
  rw [hcomponent]
  exact map_one _

end Reciprocity
end GlobalClassFieldTheory
