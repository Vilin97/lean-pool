/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueActionIndex
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteExtensionCorrespondence
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF

/-! # Local Residue Datum -/

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  hasExtension_valuation_of_valuationSubring_pullback →
    hasExtension_valuation_of_valuationSubring_pullback

open _root_.ValuationTheory.DiscreteValuationField.ValuedExtension renaming
  exists_integralClosure_standard_fundamental_identity →
    exists_integralClosure_standard_fundamental_identity

open _root_.ValuationTheory.DiscreteValuationField.ValuedExtension renaming
  target_valuationSubring_eq_of_finite_separable →
    target_valuationSubring_eq_of_finite_separable

namespace LocalClassFieldTheory

open ClassFormation

open ValuationTheory RamificationTheory LocalFieldTheory

/-!
# Finite local reciprocity: the local residue degree datum

For a nonarchimedean local field `K`, this file makes the choices implicit in
the construction explicit.  The canonical local valuation is packaged as a complete
DVF, Chevalley's theorem chooses an extension to `AlgebraicClosure K`, and
that valuation is pulled back to `SeparableClosure K`.  Finite-separable
uniqueness shows that its decomposition subgroup is the whole Galois group.
The residue field of the decomposition field is then identified with the
finite residue field of `K`.

The remaining step is topological: the reduction action is shown continuous
for the two Krull topologies and is composed with the intrinsic finite-field
degree map from `ResidueAlgebraicClosureDegree`.  The selected residue field
is algebraically closed because its extension to the residue of
`AlgebraicClosure K` is purely inseparable and the selected residue field is
perfect over the finite base residue field.
-/

noncomputable section

open scoped Pointwise ValuativeRel
open HilbertRamification.ValuationSubring
open Field.absoluteGaloisGroup

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The algebraic closure is an algebra over the selected separable closure through its
inclusion. -/
local instance localSeparableClosureAlgebra :
    Algebra (SeparableClosure K) (AlgebraicClosure K) :=
  (separableClosure K (AlgebraicClosure K)).val.toRingHom.toAlgebra

local instance localSeparableClosureScalarTower :
    IsScalarTower K (SeparableClosure K) (AlgebraicClosure K) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-! ## The canonical complete discrete valuation and its absolute extension -/

/-- A Chevalley extension of the local valuation to the chosen algebraic
closure.  This is the valuation choice `w | v` made in the finite local reciprocity construction. -/
private noncomputable def localAbsoluteValuationSubring :
    ValuationSubring (AlgebraicClosure K) :=
  Classical.choose
    (ValuationTheory.DiscreteValuationField.Valuation.exists_extension_valuationSubring
      (L := AlgebraicClosure K) (localCompleteDVF K).valuation)

/-- The chosen absolute valuation ring pulls back to the canonical valuation
ring of `K`. -/
private theorem localAbsoluteValuationSubring_pullback (x : K) :
    algebraMap K (AlgebraicClosure K) x ∈
        localAbsoluteValuationSubring K ↔
      x ∈ (localCompleteDVF K).valuation.valuationSubring := by
  rcases Classical.choose_spec
      (ValuationTheory.DiscreteValuationField.Valuation.exists_extension_valuationSubring
        (L := AlgebraicClosure K) (localCompleteDVF K).valuation) with
    ⟨_hmap, _hlocal, hpullback⟩
  exact hpullback x

private noncomputable instance localAbsoluteValuationHasExtension :
    (localCompleteDVF K).valuation.HasExtension
      (localAbsoluteValuationSubring K).valuation :=
  hasExtension_valuation_of_valuationSubring_pullback
    (localCompleteDVF K).valuation (localAbsoluteValuationSubring K)
      (localAbsoluteValuationSubring_pullback K)

/-- The valuation ring on the separable closure used in finite local reciprocity.
We choose it
as the pullback of the auxiliary valuation ring on the algebraic closure. -/
noncomputable def localSeparableValuationSubring :
    ValuationSubring (SeparableClosure K) :=
  (localAbsoluteValuationSubring K).comap
    (algebraMap (SeparableClosure K) (AlgebraicClosure K))

/-- Pulling the separable valuation subring back to `K` recovers the base valuation ring. -/
theorem localSeparableValuationSubring_pullback (x : K) :
    algebraMap K (SeparableClosure K) x ∈
        localSeparableValuationSubring K ↔
      x ∈ (localCompleteDVF K).valuation.valuationSubring := by
  change algebraMap (SeparableClosure K) (AlgebraicClosure K)
      (algebraMap K (SeparableClosure K) x) ∈
        localAbsoluteValuationSubring K ↔ _
  rw [← IsScalarTower.algebraMap_apply K (SeparableClosure K)
    (AlgebraicClosure K)]
  exact localAbsoluteValuationSubring_pullback K x

/-- The valuation on the separable closure extends the base discrete valuation. -/
noncomputable instance localSeparableValuationHasExtension :
    (localCompleteDVF K).valuation.HasExtension
      (localSeparableValuationSubring K).valuation :=
  hasExtension_valuation_of_valuationSubring_pullback
    (localCompleteDVF K).valuation (localSeparableValuationSubring K)
      (localSeparableValuationSubring_pullback K)

/-- The extension valuation on the separable closure is independent of the
auxiliary Chevalley choice.  Equality is checked at the finite separable
field generated by one element and follows there from Henselian uniqueness. -/
theorem localSeparableValuationSubring_eq_of_hasExtension
    (B : ValuationSubring (SeparableClosure K))
    [(localCompleteDVF K).valuation.HasExtension B.valuation] :
    localSeparableValuationSubring K = B := by
  ext z
  let E : IntermediateField K (SeparableClosure K) :=
    IntermediateField.adjoin K ({z} : Set (SeparableClosure K))
  let : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral z)
  let : Algebra.IsSeparable K E := inferInstance
  obtain ⟨target, hExt, _hIntegralClosure, _hFundamental⟩ :=
    exists_integralClosure_standard_fundamental_identity
      (K := K) (L := E) (localCompleteDVF K)
  let : (localCompleteDVF K).valuation.HasExtension target.valuation := hExt
  let : IsScalarTower (localCompleteDVF K).valuationSubring
      target.valuationSubring E :=
    ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_isScalarTower_of_hasExtension
      (localCompleteDVF K).valuation target.valuation
  let Ares := (localSeparableValuationSubring K).restrictIntermediateField E
  let Bres := B.restrictIntermediateField E
  let : (localCompleteDVF K).valuation.HasExtension Ares.valuation :=
    RamificationTheory.ValuationSubring.restrictIntermediateField_hasExtension
      (localCompleteDVF K).valuation (localSeparableValuationSubring K) E
  let : (localCompleteDVF K).valuation.HasExtension Bres.valuation :=
    RamificationTheory.ValuationSubring.restrictIntermediateField_hasExtension
      (localCompleteDVF K).valuation B E
  have hA : target.valuation.valuationSubring = Ares :=
    target_valuationSubring_eq_of_finite_separable
      (localCompleteDVF K) target Ares
  have hB : target.valuation.valuationSubring = Bres :=
    target_valuationSubring_eq_of_finite_separable
      (localCompleteDVF K) target Bres
  have hAB : Ares = Bres := hA.symm.trans hB
  let zE : E :=
    ⟨z, IntermediateField.subset_adjoin (F := K)
      (S := ({z} : Set (SeparableClosure K))) (by simp)⟩
  change zE ∈ Ares ↔ zE ∈ Bres
  rw [hAB]

/-- Every automorphism of the separable closure preserves the unique
extension of the Henselian local valuation. -/
theorem localSeparableDecompositionGroup_eq_top :
    decompositionGroup K (localSeparableValuationSubring K) = ⊤ := by
  apply top_unique
  intro sigma _hsigma
  change sigma • localSeparableValuationSubring K =
    localSeparableValuationSubring K
  let : (localCompleteDVF K).valuation.HasExtension
      (sigma • localSeparableValuationSubring K).valuation :=
    RamificationTheory.ValuationSubring.smul_hasExtension
      (localCompleteDVF K).valuation (localSeparableValuationSubring K) sigma
  exact (localSeparableValuationSubring_eq_of_hasExtension K
    (sigma • localSeparableValuationSubring K)).symm

/-! ## Identification of the finite base residue field -/

/-- When the decomposition subgroup is top, the valuation ring on the
decomposition field is the original local valuation ring. -/
private noncomputable def localBaseValuationSubringEquivDecompositionField :
    (localCompleteDVF K).valuationSubring ≃+*
      decompositionFieldValuationSubring K
        (localSeparableValuationSubring K) := by
  let A := localSeparableValuationSubring K
  let Z := decompositionField K A
  have hZ : Z = ⊥ := by
    change IntermediateField.fixedField (decompositionGroup K A) = ⊥
    rw [localSeparableDecompositionGroup_eq_top K]
    simpa using
      (InfiniteGalois.fixedField_fixingSubgroup
        (⊥ : IntermediateField K (SeparableClosure K)))
  let eKZ : K ≃ₐ[K] Z :=
    (IntermediateField.botEquiv K (SeparableClosure K)).symm.trans
      (IntermediateField.equivOfEq hZ.symm)
  refine
    { toFun := fun x => ⟨eKZ (x : K), ?_⟩
      invFun := fun z => ⟨eKZ.symm (z : Z), ?_⟩
      left_inv := fun x => by
        apply Subtype.ext
        exact eKZ.symm_apply_apply (x : K)
      right_inv := fun z => by
        apply Subtype.ext
        exact eKZ.apply_symm_apply (z : Z)
      map_add' := fun x y => by
        apply Subtype.ext
        exact map_add eKZ (x : K) (y : K)
      map_mul' := fun x y => by
        apply Subtype.ext
        exact map_mul eKZ (x : K) (y : K) }
  · change ((eKZ x : Z) : SeparableClosure K) ∈ A
    have he : ((eKZ x : Z) : SeparableClosure K) =
        algebraMap K (SeparableClosure K) (x : K) := by
      rfl
    rw [he]
    exact (localSeparableValuationSubring_pullback K (x : K)).2 x.property
  · change eKZ.symm (z : Z) ∈
      (localCompleteDVF K).valuation.valuationSubring
    apply (localSeparableValuationSubring_pullback K (eKZ.symm (z : Z))).1
    have he : algebraMap K (SeparableClosure K) (eKZ.symm (z : Z)) =
        ((z : Z) : SeparableClosure K) := by
      exact congrArg Subtype.val (eKZ.apply_symm_apply (z : Z))
    rw [he]
    exact z.property

/-- The residue field in the residue-action exact sequence is canonically the finite residue
field of the original local field. -/
noncomputable def localBaseResidueEquivDecompositionResidue :
    (localCompleteDVF K).residueField ≃+*
      decompositionResidueField K (localSeparableValuationSubring K) :=
  (IsLocalRing.ResidueField.mapEquiv
      (localBaseValuationSubringEquivDecompositionField K)).trans
    (decompositionFieldResidueEquiv (K := K)
      (localSeparableValuationSubring K))

/-- Naturality of the base-residue comparison with the literal reduction
map into the selected residue field.  This is the scalar square used when
transporting residue degrees from the residue-action presentation back
to the canonical residue fields of local extensions. -/
theorem localBaseResidueEquivDecompositionResidue_algebraMap
    (x : (localCompleteDVF K).valuationSubring) :
    algebraMap
        (decompositionResidueField K (localSeparableValuationSubring K))
        (selectedResidueField (localSeparableValuationSubring K))
        (localBaseResidueEquivDecompositionResidue K
          (IsLocalRing.residue (localCompleteDVF K).valuationSubring x)) =
      IsLocalRing.residue (localSeparableValuationSubring K)
        (⟨algebraMap K (SeparableClosure K) (x : K),
          (localSeparableValuationSubring_pullback K (x : K)).2
            x.property⟩ : localSeparableValuationSubring K) := by
  rfl

/-- The residue field attached to the local decomposition datum is finite. -/
noncomputable instance localDecompositionResidueFinite :
    Finite (decompositionResidueField K
      (localSeparableValuationSubring K)) := by
  have : Finite (localCompleteDVF K).residueField := by
    change Finite 𝓀[K]
    infer_instance
  exact Finite.of_equiv (localCompleteDVF K).residueField
    (localBaseResidueEquivDecompositionResidue K).toEquiv

/-- The finite local decomposition residue field has a canonical finite enumeration. -/
noncomputable instance localDecompositionResidueFintype :
    Fintype (decompositionResidueField K
      (localSeparableValuationSubring K)) :=
  Fintype.ofFinite _

/-- The selected residue field of the separable valuation is algebraically closed. -/
instance localSelectedResidueIsAlgClosed :
    IsAlgClosed (selectedResidueField
      (localSeparableValuationSubring K)) := by
  let A := localAbsoluteValuationSubring K
  let B := localSeparableValuationSubring K
  let barI := valuationSubringComapResidueMap
    (F := SeparableClosure K) A
  let : Algebra (selectedResidueField B) (selectedResidueField A) :=
    barI.toAlgebra
  let : IsPurelyInseparable (SeparableClosure K) (AlgebraicClosure K) :=
    separableClosure.isPurelyInseparable K (AlgebraicClosure K)
  let : IsPurelyInseparable (selectedResidueField B)
      (selectedResidueField A) :=
    valuationSubring_comap_residueField_isPurelyInseparable
      (F := SeparableClosure K) A
  let : PerfectField (decompositionResidueField K B) := inferInstance
  let : Algebra.IsAlgebraic (decompositionResidueField K B)
      (selectedResidueField B) := inferInstance
  let : PerfectField (selectedResidueField B) :=
    Algebra.IsAlgebraic.perfectField
      (K := decompositionResidueField K B)
      (L := selectedResidueField B)
  let : Algebra.IsSeparable (selectedResidueField B)
      (selectedResidueField A) := inferInstance
  have hsurjective : Function.Surjective barI :=
    IsPurelyInseparable.surjective_algebraMap_of_isSeparable
      (selectedResidueField B) (selectedResidueField A)
  let e : selectedResidueField B ≃+* selectedResidueField A :=
    RingEquiv.ofBijective barI ⟨barI.injective, hsurjective⟩
  let : IsAlgClosed (selectedResidueField A) :=
    valuationSubring_residueField_isAlgClosed A
  exact IsAlgClosed.of_ringEquiv (selectedResidueField A)
    (selectedResidueField B) e.symm

/-! ## Continuity of reduction and the local degree map -/

/-- A fixed representative in the chosen valuation ring of a residue class. -/
private noncomputable def localSelectedResidueLift
    (x : selectedResidueField (localSeparableValuationSubring K)) :
    localSeparableValuationSubring K :=
  Classical.choose (IsLocalRing.residue_surjective x)

@[simp]
private theorem localSelectedResidueLift_residue
    (x : selectedResidueField (localSeparableValuationSubring K)) :
    IsLocalRing.residue (localSeparableValuationSubring K)
        (localSelectedResidueLift K x) = x :=
  Classical.choose_spec (IsLocalRing.residue_surjective x)

/-- Reduction from the absolute Galois group to the absolute Galois group of
the residue field is continuous for the Krull topologies.  A finite residue
subextension is controlled by adjoining to `K` one lift of each of its
finitely many elements. -/
private theorem localSeparableResidueAlgAction_continuous :
    Continuous
      (residueAlgActionOfEqTop K
        (localSeparableValuationSubring K)
        (localSeparableDecompositionGroup_eq_top K)) := by
  classical
  let A := localSeparableValuationSubring K
  let k : Type := decompositionResidueField K A
  let Omega : Type := selectedResidueField A
  let hA := localSeparableDecompositionGroup_eq_top K
  let rho := residueAlgActionOfEqTop K A hA
  refine continuous_of_continuousAt_one rho ?_
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro s hs
  rw [Filter.mem_map]
  rcases (krullTopology_mem_nhds_one_iff k Omega s).1 hs with
    ⟨E, hE, hEs⟩
  let : Algebra k E := E.algebra
  let : FiniteDimensional k E := hE
  let : Finite E := Module.finite_of_finite
    (decompositionResidueField K (localSeparableValuationSubring K))
  let : Fintype E := Fintype.ofFinite E
  let lifts : Finset (SeparableClosure K) :=
    Finset.univ.image (fun x : E =>
      ((localSelectedResidueLift K (x : Omega) : A) : SeparableClosure K))
  let F : IntermediateField K (SeparableClosure K) :=
    IntermediateField.adjoin K (lifts : Set (SeparableClosure K))
  let : FiniteDimensional K F :=
    IntermediateField.finiteDimensional_adjoin (fun x _hx =>
      Algebra.IsIntegral.isIntegral x)
  refine (krullTopology_mem_nhds_one_iff K (SeparableClosure K)
    (rho ⁻¹' s)).2 ?_
  refine ⟨F, inferInstance, ?_⟩
  intro sigma hsigma
  apply hEs
  change rho sigma ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  let y : E := ⟨x, hx⟩
  let a : A := localSelectedResidueLift K (y : Omega)
  have ha_lifts : (a : SeparableClosure K) ∈ lifts := by
    apply Finset.mem_image.mpr
    exact ⟨y, Finset.mem_univ y, rfl⟩
  have haF : (a : SeparableClosure K) ∈ F :=
    IntermediateField.subset_adjoin (F := K)
      (S := (lifts : Set (SeparableClosure K))) ha_lifts
  have hfix : sigma (a : SeparableClosure K) = (a : SeparableClosure K) :=
    (IntermediateField.mem_fixingSubgroup_iff F sigma).mp hsigma
      (a : SeparableClosure K) haF
  change rho sigma (y : Omega) = (y : Omega)
  rw [← localSelectedResidueLift_residue K (y : Omega)]
  change IsLocalRing.residue A
      ((toDecompositionGroupOfEqTop
        K A hA sigma) • a) = IsLocalRing.residue A a
  congr 1
  apply Subtype.ext
  exact hfix

/-- The continuous residue action on the chosen residue algebraic closure. -/
noncomputable def localSeparableResidueAlgAction :
    Gal(SeparableClosure K/K) →ₜ*
      (selectedResidueField (localSeparableValuationSubring K) ≃ₐ[
        decompositionResidueField K (localSeparableValuationSubring K)]
          selectedResidueField (localSeparableValuationSubring K)) where
  toMonoidHom :=
    residueAlgActionOfEqTop K
      (localSeparableValuationSubring K)
      (localSeparableDecompositionGroup_eq_top K)
  continuous_toFun := localSeparableResidueAlgAction_continuous K

/-- Every automorphism of the selected residue extension lifts to the separable Galois group. -/
theorem localSeparableResidueAlgAction_surjective :
    Function.Surjective (localSeparableResidueAlgAction K) :=
  residueAlgActionOfEqTop_surjective K
    (localSeparableValuationSubring K)
    (localSeparableDecompositionGroup_eq_top K)

/-- **Finite local reciprocity, local degree map.**  The residue Frobenius degree,
defined directly on the separable-closure model used by the local reciprocity
formalization. -/
noncomputable def localResidueDegree :
    Gal(SeparableClosure K/K) →ₜ* ZHatMul where
  toMonoidHom :=
    (residueAbsoluteDegreeIn
      (decompositionResidueField K (localSeparableValuationSubring K))
      (selectedResidueField (localSeparableValuationSubring K))).toMonoidHom.comp
        (localSeparableResidueAlgAction K).toMonoidHom
  continuous_toFun :=
    (residueAbsoluteDegreeIn
      (decompositionResidueField K (localSeparableValuationSubring K))
      (selectedResidueField
        (localSeparableValuationSubring K))).continuous_toFun.comp
      (localSeparableResidueAlgAction K).continuous_toFun

/-- The local residue-degree map onto the profinite integers is surjective. -/
theorem localResidueDegree_surjective :
    Function.Surjective (localResidueDegree K) := by
  intro z
  obtain ⟨tau, htau⟩ :=
    (residueDatumIn
      (decompositionResidueField K (localSeparableValuationSubring K))
      (selectedResidueField
        (localSeparableValuationSubring K))).degree_surjective z
  obtain ⟨sigma, hsigma⟩ :=
    localSeparableResidueAlgAction_surjective K tau
  refine ⟨sigma, ?_⟩
  change residueAbsoluteDegreeIn
      (decompositionResidueField K (localSeparableValuationSubring K))
      (selectedResidueField (localSeparableValuationSubring K))
        (localSeparableResidueAlgAction K sigma) = z
  rw [hsigma]
  simpa [residueDatumIn] using htau

/-- **Finite local reciprocity.**  The actual abstract class-formation datum
`d : G_K -> ZHat` furnished by the residue action of a local field. -/
noncomputable def localResidueDatum :
    DegreeData (Gal(SeparableClosure K/K)) where
  degree := localResidueDegree K
  degree_surjective := localResidueDegree_surjective K

end
end LocalClassFieldTheory
