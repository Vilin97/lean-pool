/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

The concrete spatial crossed-product bridge for Zhou §3. Character
multipliers generate the continuous-coefficient crossed closure by uniform
Stone--Weierstrass density; the fiber shear transports that closure and hence
the two regular group factors.
-/
import LeanPool.ConnesRigidity.Paper.Section3.GroupQuotient
import LeanPool.ConnesRigidity.Foundation.OperatorAlgebra.SemidirectClosure
import LeanPool.ConnesRigidity.Foundation.OperatorAlgebra.CrossedProductFactorTransport
import LeanPool.ConnesRigidity.Paper.Section3.GroupVacuum
import LeanPool.ConnesRigidity.Foundation.OperatorAlgebra.SemidirectGeneratorTransport
import LeanPool.ConnesRigidity.Foundation.OperatorAlgebra.FactorWitness

/-!
The factor closure component of the Connes rigidity formalization.
-/

namespace Connes
namespace PaperFactorClosure

open Construction
open Construction.PaperKernel
open PaperCrossedHaar
open PaperCrossedKernel
open PaperFourier
open PaperFourierCoordinates
open PaperDualTopology
open PaperGroupFactor
open PaperGroupQuotient
open PaperGroupVacuum
open CrossedProduct
open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

/--
The `D` construction used in the Connes rigidity formalization.
-/
abbrev D := PaperKernel.D
/--
The `H` construction used in the Connes rigidity formalization.
-/
abbrev H := Construction.H
local notation "Γ₁" => PaperKernel.paperGammaCarrier paperThetaOneHom
local notation "Γ₂" => PaperKernel.paperGammaCarrier paperThetaTwoHom

local instance paperHaarProbability
    (X : HaarProbabilityAction H PaperFactorIsomorphism.DualCoordinates) :
    IsProbabilityMeasure X.measure :=
  X.probability

private theorem leftRegularRepresentation_apply_clm
    {G : Type*} [Group G] (g : G) :
    ((leftRegularRepresentation G g :
        unitary (GroupL2 G →L[ℂ] GroupL2 G)) :
      GroupL2 G →L[ℂ] GroupL2 G) =
      ((leftRegularUnitary g :
          unitary (GroupL2 G →L[ℂ] GroupL2 G)) :
        GroupL2 G →L[ℂ] GroupL2 G) := rfl

/--
The `reducedCrossedGeneratorSetOne` construction used in the Connes rigidity formalization.
-/
def reducedCrossedGeneratorSetOne :
    Set (CrossedOne →L[ℂ] CrossedOne) :=
  Set.range crossedKernelMultiplier ∪
    Set.range fun h : H ↦
      (crossedGroupUnitary paperHaarActionOne h).toContinuousLinearEquiv.toContinuousLinearMap

/--
The `reducedCrossedGeneratorSetTwo` construction used in the Connes rigidity formalization.
-/
def reducedCrossedGeneratorSetTwo :
    Set (CrossedTwo →L[ℂ] CrossedTwo) :=
  (Set.range fun d : D ↦
      crossedMultiplier paperHaarActionTwo (coordinateCharacterCoefficient d)) ∪
    Set.range fun h : H ↦
      (crossedGroupUnitary paperHaarActionTwo h).toContinuousLinearEquiv.toContinuousLinearMap

theorem paperGroupFactorUnitaryOne_generatorSet_image :
    paperGroupFactorUnitaryOne.conjStarAlgEquiv ''
        SemidirectGeneratorTransport.generatorSet
          (A := Multiplicative D) (K := H) paperThetaOneHom =
      reducedCrossedGeneratorSetOne := by
  ext T
  constructor
  · rintro ⟨S, (⟨a, rfl⟩ | ⟨h, rfl⟩), rfl⟩
    · left
      refine ⟨Multiplicative.toAdd a, ?_⟩
      simpa only [leftRegularRepresentation_apply_clm, ofAdd_toAdd] using
        (paperGroupFactorUnitaryOne_conj_inl
          (Multiplicative.toAdd a)).symm
    · right
      exact ⟨h, (paperGroupFactorUnitaryOne_conj_inr h).symm⟩
  · rintro (⟨d, rfl⟩ | ⟨h, rfl⟩)
    · refine ⟨_, Or.inl ⟨Multiplicative.ofAdd d, rfl⟩, ?_⟩
      exact paperGroupFactorUnitaryOne_conj_inl d
    · refine ⟨_, Or.inr ⟨h, rfl⟩, ?_⟩
      exact paperGroupFactorUnitaryOne_conj_inr h

theorem paperGroupFactorUnitaryTwo_generatorSet_image :
    paperGroupFactorUnitaryTwo.conjStarAlgEquiv ''
        SemidirectGeneratorTransport.generatorSet
          (A := Multiplicative D) (K := H) paperThetaTwoHom =
      reducedCrossedGeneratorSetTwo := by
  ext T
  constructor
  · rintro ⟨S, (⟨a, rfl⟩ | ⟨h, rfl⟩), rfl⟩
    · left
      refine ⟨Multiplicative.toAdd a, ?_⟩
      simpa only [leftRegularRepresentation_apply_clm, ofAdd_toAdd] using
        (paperGroupFactorUnitaryTwo_conj_inl
          (Multiplicative.toAdd a)).symm
    · right
      exact ⟨h, (paperGroupFactorUnitaryTwo_conj_inr h).symm⟩
  · rintro (⟨d, rfl⟩ | ⟨h, rfl⟩)
    · refine ⟨_, Or.inl ⟨Multiplicative.ofAdd d, rfl⟩, ?_⟩
      exact paperGroupFactorUnitaryTwo_conj_inl d
    · refine ⟨_, Or.inr ⟨h, rfl⟩, ?_⟩
      exact paperGroupFactorUnitaryTwo_conj_inr h

theorem paperGroupFactorUnitaryOne_mem_reducedClosure_iff
    (T : GroupL2 Γ₁ →L[ℂ] GroupL2 Γ₁) :
    T ∈ vonNeumannClosure
        (Set.range fun x : Γ₁ ↦
          (leftRegularRepresentation Γ₁ x :
            GroupL2 Γ₁ →L[ℂ] GroupL2 Γ₁)) ↔
      paperGroupFactorUnitaryOne.conjStarAlgEquiv T ∈
        vonNeumannClosure reducedCrossedGeneratorSetOne := by
  change T ∈ vonNeumannClosure
      (Set.range fun x : (Multiplicative D ⋊[paperThetaOneHom] H) ↦
        (leftRegularRepresentation (Multiplicative D ⋊[paperThetaOneHom] H) x :
          GroupL2 (Multiplicative D ⋊[paperThetaOneHom] H) →L[ℂ]
            GroupL2 (Multiplicative D ⋊[paperThetaOneHom] H))) ↔ _
  calc
    T ∈ vonNeumannClosure
        (Set.range fun x : (Multiplicative D ⋊[paperThetaOneHom] H) ↦
          (leftRegularRepresentation (Multiplicative D ⋊[paperThetaOneHom] H) x :
            GroupL2 (Multiplicative D ⋊[paperThetaOneHom] H) →L[ℂ]
              GroupL2 (Multiplicative D ⋊[paperThetaOneHom] H))) ↔
        T ∈ vonNeumannClosure
          (SemidirectGeneratorTransport.generatorSet paperThetaOneHom) :=
      Iff.of_eq (congrArg (fun M : VonNeumannAlgebra (GroupL2 Γ₁) ↦
        T ∈ M) (semidirect_vonNeumannClosure_eq_inl_inr
          (A := Multiplicative D) (K := H) paperThetaOneHom))
    _ ↔ paperGroupFactorUnitaryOne.conjStarAlgEquiv T ∈
        vonNeumannClosure reducedCrossedGeneratorSetOne :=
      by
        apply mem_vonNeumannClosure_iff_of_conj_image_eq
        exact paperGroupFactorUnitaryOne_generatorSet_image

theorem paperGroupFactorUnitaryTwo_mem_reducedClosure_iff
    (T : GroupL2 Γ₂ →L[ℂ] GroupL2 Γ₂) :
    T ∈ vonNeumannClosure
        (Set.range fun x : Γ₂ ↦
          (leftRegularRepresentation Γ₂ x :
            GroupL2 Γ₂ →L[ℂ] GroupL2 Γ₂)) ↔
      paperGroupFactorUnitaryTwo.conjStarAlgEquiv T ∈
        vonNeumannClosure reducedCrossedGeneratorSetTwo := by
  change T ∈ vonNeumannClosure
      (Set.range fun x : (Multiplicative D ⋊[paperThetaTwoHom] H) ↦
        (leftRegularRepresentation (Multiplicative D ⋊[paperThetaTwoHom] H) x :
          GroupL2 (Multiplicative D ⋊[paperThetaTwoHom] H) →L[ℂ]
            GroupL2 (Multiplicative D ⋊[paperThetaTwoHom] H))) ↔ _
  calc
    T ∈ vonNeumannClosure
        (Set.range fun x : (Multiplicative D ⋊[paperThetaTwoHom] H) ↦
          (leftRegularRepresentation (Multiplicative D ⋊[paperThetaTwoHom] H) x :
            GroupL2 (Multiplicative D ⋊[paperThetaTwoHom] H) →L[ℂ]
              GroupL2 (Multiplicative D ⋊[paperThetaTwoHom] H))) ↔
        T ∈ vonNeumannClosure
          (SemidirectGeneratorTransport.generatorSet paperThetaTwoHom) :=
      Iff.of_eq (congrArg (fun M : VonNeumannAlgebra (GroupL2 Γ₂) ↦
        T ∈ M) (semidirect_vonNeumannClosure_eq_inl_inr
          (A := Multiplicative D) (K := H) paperThetaTwoHom))
    _ ↔ paperGroupFactorUnitaryTwo.conjStarAlgEquiv T ∈
        vonNeumannClosure reducedCrossedGeneratorSetTwo :=
      by
        apply mem_vonNeumannClosure_iff_of_conj_image_eq
        exact paperGroupFactorUnitaryTwo_generatorSet_image

theorem coordinateComplexCharacter_star (d : D) :
    star (coordinateComplexCharacter d) =
      coordinateComplexCharacter (-d) := by
  ext p
  change starRingEnd ℂ
      (complexCharacter d (characterCoordinatesHomeomorph.symm p)) =
    complexCharacter (-d) (characterCoordinatesHomeomorph.symm p)
  exact DFunLike.congr_fun (PaperFourier.complexCharacter_star d)
    (characterCoordinatesHomeomorph.symm p)

/--
The `coordinateCharacterSubalgebra` construction used in the Connes rigidity formalization.
-/
def coordinateCharacterSubalgebra :
    StarSubalgebra ℂ C(PaperFactorIsomorphism.DualCoordinates, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ
    (Set.range (coordinateComplexCharacter : D →
      C(PaperFactorIsomorphism.DualCoordinates, ℂ)))
  star_mem' := by
    change Algebra.adjoin ℂ (Set.range (coordinateComplexCharacter : D →
      C(PaperFactorIsomorphism.DualCoordinates, ℂ))) ≤
        star (Algebra.adjoin ℂ
          (Set.range (coordinateComplexCharacter : D →
            C(PaperFactorIsomorphism.DualCoordinates, ℂ))))
    refine Algebra.adjoin_le ?_
    rintro _ ⟨d, rfl⟩
    exact Algebra.subset_adjoin ⟨-d, (coordinateComplexCharacter_star d).symm⟩

theorem coordinateCharacterSubalgebra_toSubmodule :
    coordinateCharacterSubalgebra.toSubalgebra.toSubmodule =
      Submodule.span ℂ (Set.range (coordinateComplexCharacter : D →
        C(PaperFactorIsomorphism.DualCoordinates, ℂ))) := by
  apply Algebra.adjoin_eq_span_of_subset
  refine Set.Subset.trans ?_ Submodule.subset_span
  intro z hz
  refine Submonoid.closure_induction (fun _ ↦ id) ⟨0, ?_⟩ ?_ hz
  · ext p
    simp [coordinateComplexCharacter, PaperFourier.complexCharacter]
  · rintro - - - - ⟨d, rfl⟩ ⟨e, rfl⟩
    refine ⟨d + e, ?_⟩
    ext p
    simp [coordinateComplexCharacter, PaperFourier.complexCharacter]

theorem coordinateComplexCharacter_span_closure_eq_top :
    (Submodule.span ℂ (Set.range (coordinateComplexCharacter : D →
      C(PaperFactorIsomorphism.DualCoordinates, ℂ)))).topologicalClosure = ⊤ := by
  have hsep : coordinateCharacterSubalgebra.SeparatesPoints := by
    intro p q hpq
    have hpq' : characterCoordinatesHomeomorph.symm p ≠
        characterCoordinatesHomeomorph.symm q := by
      intro h
      exact hpq (characterCoordinatesHomeomorph.symm.injective h)
    obtain ⟨d, hd⟩ := PaperFourier.complexCharacter_separates hpq'
    refine ⟨_, ⟨coordinateComplexCharacter d,
      Algebra.subset_adjoin ⟨d, rfl⟩, rfl⟩, ?_⟩
    exact hd
  rw [← coordinateCharacterSubalgebra_toSubmodule]
  exact congrArg (Subalgebra.toSubmodule ∘ StarSubalgebra.toSubalgebra)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
      coordinateCharacterSubalgebra hsep)

theorem continuousCrossedMultiplier_coordinate_one (d : D) :
    continuousCrossedMultiplier paperHaarActionOne
        (coordinateComplexCharacter d) = crossedKernelMultiplier d := by
  rw [continuousCrossedMultiplier_apply]
  rfl

theorem continuousCrossedMultiplier_coordinate_two (d : D) :
    continuousCrossedMultiplier paperHaarActionTwo
        (coordinateComplexCharacter d) =
      crossedMultiplier paperHaarActionTwo (coordinateCharacterCoefficient d) := by
  rw [continuousCrossedMultiplier_apply]
  rfl

/--
The `continuousCrossedGeneratorSetOne` construction used in the Connes rigidity formalization.
-/
def continuousCrossedGeneratorSetOne :
    Set (CrossedOne →L[ℂ] CrossedOne) :=
  continuousCrossedGeneratorSet paperHaarActionOne

/--
The `continuousCrossedGeneratorSetTwo` construction used in the Connes rigidity formalization.
-/
def continuousCrossedGeneratorSetTwo :
    Set (CrossedTwo →L[ℂ] CrossedTwo) :=
  continuousCrossedGeneratorSet paperHaarActionTwo

theorem reducedCrossedGeneratorSetOne_eq_continuousCoefficients :
    reducedCrossedGeneratorSetOne =
      crossedGeneratorSetOfContinuousCoefficients paperHaarActionOne
        coordinateComplexCharacter := by
  ext T
  constructor
  · rintro (⟨d, rfl⟩ | ⟨h, rfl⟩)
    · exact Or.inl ⟨d, continuousCrossedMultiplier_coordinate_one d⟩
    · exact Or.inr ⟨h, rfl⟩
  · rintro (⟨d, rfl⟩ | ⟨h, rfl⟩)
    · exact Or.inl ⟨d, (continuousCrossedMultiplier_coordinate_one d).symm⟩
    · exact Or.inr ⟨h, rfl⟩

theorem reducedCrossedGeneratorSetTwo_eq_continuousCoefficients :
    reducedCrossedGeneratorSetTwo =
      crossedGeneratorSetOfContinuousCoefficients paperHaarActionTwo
        coordinateComplexCharacter := by
  ext T
  constructor
  · rintro (⟨d, rfl⟩ | ⟨h, rfl⟩)
    · exact Or.inl ⟨d, continuousCrossedMultiplier_coordinate_two d⟩
    · exact Or.inr ⟨h, rfl⟩
  · rintro (⟨d, rfl⟩ | ⟨h, rfl⟩)
    · exact Or.inl ⟨d, (continuousCrossedMultiplier_coordinate_two d).symm⟩
    · exact Or.inr ⟨h, rfl⟩

theorem reducedClosureOne_eq_continuousClosure :
    vonNeumannClosure reducedCrossedGeneratorSetOne =
      vonNeumannClosure continuousCrossedGeneratorSetOne := by
  rw [reducedCrossedGeneratorSetOne_eq_continuousCoefficients]
  exact vonNeumannClosure_crossedGeneratorSetOfContinuousCoefficients_eq
    paperHaarActionOne coordinateComplexCharacter
    coordinateComplexCharacter_span_closure_eq_top

theorem reducedClosureTwo_eq_continuousClosure :
    vonNeumannClosure reducedCrossedGeneratorSetTwo =
      vonNeumannClosure continuousCrossedGeneratorSetTwo := by
  rw [reducedCrossedGeneratorSetTwo_eq_continuousCoefficients]
  exact vonNeumannClosure_crossedGeneratorSetOfContinuousCoefficients_eq
    paperHaarActionTwo coordinateComplexCharacter
    coordinateComplexCharacter_span_closure_eq_top

theorem paperHaarEquiv_mem_continuousClosure_iff
    (T : CrossedOne →L[ℂ] CrossedOne) :
    T ∈ vonNeumannClosure continuousCrossedGeneratorSetOne ↔
      (crossedHaarHilbertEquiv paperHaarEquiv).conjStarAlgEquiv T ∈
        vonNeumannClosure continuousCrossedGeneratorSetTwo := by
  simpa [continuousCrossedGeneratorSetOne,
    continuousCrossedGeneratorSetTwo, paperHaarEquiv] using
    (continuousCrossedClosure_mem_iff paperHaarHomeomorph T)

/- The two paper Fourier models and the fiber shear compose to the concrete
spatial equivalence of regular Hilbert spaces. Paper: §3.
-/
/--
The `paperSpatialUnitary` construction used in the Connes rigidity formalization.
-/
def paperSpatialUnitary :
    GroupL2 Γ₁ ≃ₗᵢ[ℂ] GroupL2 Γ₂ :=
  paperGroupFactorUnitaryOne |>.trans
    (crossedHaarHilbertEquiv paperHaarEquiv) |>.trans
      paperGroupFactorUnitaryTwo.symm

/-- The spatial equivalence carries the first regular group factor onto the
second. Paper: §3. -/
theorem paperSpatialUnitary_maps_group_factor
    (T : GroupL2 Γ₁ →L[ℂ] GroupL2 Γ₁) :
    T ∈ vonNeumannClosure
        (Set.range fun x : Γ₁ ↦
          (leftRegularRepresentation Γ₁ x :
            GroupL2 Γ₁ →L[ℂ] GroupL2 Γ₁)) ↔
      paperSpatialUnitary.conjStarAlgEquiv T ∈
        vonNeumannClosure
          (Set.range fun x : Γ₂ ↦
            (leftRegularRepresentation Γ₂ x :
              GroupL2 Γ₂ →L[ℂ] GroupL2 Γ₂)) := by
  rw [paperGroupFactorUnitaryOne_mem_reducedClosure_iff]
  change paperGroupFactorUnitaryOne.conjStarAlgEquiv T ∈
      vonNeumannClosure reducedCrossedGeneratorSetOne ↔
    paperGroupFactorUnitaryTwo.symm.conjStarAlgEquiv
        ((crossedHaarHilbertEquiv paperHaarEquiv).conjStarAlgEquiv
          (paperGroupFactorUnitaryOne.conjStarAlgEquiv T)) ∈
      vonNeumannClosure
        (Set.range fun x : Γ₂ ↦
          (leftRegularRepresentation Γ₂ x :
            GroupL2 Γ₂ →L[ℂ] GroupL2 Γ₂))
  let S := paperGroupFactorUnitaryOne.conjStarAlgEquiv T
  let R := (crossedHaarHilbertEquiv paperHaarEquiv).conjStarAlgEquiv S
  calc
    S ∈ vonNeumannClosure reducedCrossedGeneratorSetOne ↔
        S ∈ vonNeumannClosure continuousCrossedGeneratorSetOne := by
      exact Iff.of_eq (congrArg (fun U ↦ S ∈ U)
        reducedClosureOne_eq_continuousClosure)
    _ ↔ R ∈ vonNeumannClosure continuousCrossedGeneratorSetTwo :=
      paperHaarEquiv_mem_continuousClosure_iff S
    _ ↔ R ∈ vonNeumannClosure reducedCrossedGeneratorSetTwo := by
      exact Iff.of_eq (congrArg (fun U ↦ R ∈ U)
        reducedClosureTwo_eq_continuousClosure.symm)
    _ ↔ paperGroupFactorUnitaryTwo.symm.conjStarAlgEquiv R ∈
        vonNeumannClosure
          (Set.range fun x : Γ₂ ↦
            (leftRegularRepresentation Γ₂ x :
              GroupL2 Γ₂ →L[ℂ] GroupL2 Γ₂)) := by
      let X := paperGroupFactorUnitaryTwo.symm.conjStarAlgEquiv R
      have hR : paperGroupFactorUnitaryTwo.conjStarAlgEquiv
          X = R := by
        exact paperGroupFactorUnitaryTwo.conjStarAlgEquiv.apply_symm_apply R
      calc
        R ∈ vonNeumannClosure reducedCrossedGeneratorSetTwo ↔
            paperGroupFactorUnitaryTwo.conjStarAlgEquiv X ∈
              vonNeumannClosure reducedCrossedGeneratorSetTwo :=
          Iff.of_eq (congrArg (fun Z : CrossedTwo →L[ℂ] CrossedTwo ↦
            Z ∈ vonNeumannClosure reducedCrossedGeneratorSetTwo) hR.symm)
        _ ↔ X ∈ vonNeumannClosure
            (Set.range fun x : Γ₂ ↦
              (leftRegularRepresentation Γ₂ x :
                GroupL2 Γ₂ →L[ℂ] GroupL2 Γ₂)) :=
          (paperGroupFactorUnitaryTwo_mem_reducedClosure_iff X).symm

/- The spatial equivalence preserves the canonical group vacuum. Paper: §3. -/
theorem paperSpatialUnitary_maps_vacuum :
    paperSpatialUnitary paperIdentityOne = paperIdentityTwo := by
  change paperGroupFactorUnitaryTwo.symm
      (crossedHaarHilbertEquiv paperHaarEquiv
        (paperGroupFactorUnitaryOne paperIdentityOne)) = paperIdentityTwo
  calc
    _ = paperGroupFactorUnitaryTwo.symm
        (crossedHaarHilbertEquiv paperHaarEquiv
          (crossedVacuum paperHaarActionOne)) := congrArg
            (fun ξ ↦ paperGroupFactorUnitaryTwo.symm
              (crossedHaarHilbertEquiv paperHaarEquiv ξ))
            paperGroupFactorUnitaryOne_vacuum
    _ = paperGroupFactorUnitaryTwo.symm
        (crossedVacuum paperHaarActionTwo) := congrArg
          paperGroupFactorUnitaryTwo.symm
          (crossedHaarHilbertEquiv_vacuum paperHaarEquiv)
    _ = paperGroupFactorUnitaryTwo.symm
        (paperGroupFactorUnitaryTwo paperIdentityTwo) := congrArg
          paperGroupFactorUnitaryTwo.symm
          paperGroupFactorUnitaryTwo_vacuum.symm
    _ = paperIdentityTwo := paperGroupFactorUnitaryTwo.symm_apply_apply _

/- The concrete spatial witness for Zhou's pair of group factors. Paper: §3.
-/
/--
The `paperSpatialWitness` construction used in the Connes rigidity formalization.
-/
def paperSpatialWitness : FactorWitness.SpatialWitness
    paperGammaOne paperGammaTwo where
  unitary := by
    change GroupL2 Γ₁ ≃ₗᵢ[ℂ] GroupL2 Γ₂
    exact paperSpatialUnitary
  maps_group_factor := by
    intro T
    unfold groupVonNeumannAlgebra
    change T ∈ vonNeumannClosure
        (Set.range fun x : Γ₁ ↦
          (leftRegularRepresentation Γ₁ x :
            GroupL2 Γ₁ →L[ℂ] GroupL2 Γ₁)) ↔
      paperSpatialUnitary.conjStarAlgEquiv T ∈
        vonNeumannClosure
          (Set.range fun x : Γ₂ ↦
            (leftRegularRepresentation Γ₂ x :
              GroupL2 Γ₂ →L[ℂ] GroupL2 Γ₂))
    exact paperSpatialUnitary_maps_group_factor T
  maps_vacuum := by
    change paperSpatialUnitary paperIdentityOne = paperIdentityTwo
    exact paperSpatialUnitary_maps_vacuum

/- The two concrete paper group factors are trace-preservingly isomorphic.
Paper: §3. -/
theorem paperGroupFactors_isomorphic :
    TracialGroupFactorsIsomorphic
      paperGammaOne paperGammaTwo :=
  FactorWitness.tracialEquiv_of_spatialWitness paperSpatialWitness

end
end PaperFactorClosure
end Connes
