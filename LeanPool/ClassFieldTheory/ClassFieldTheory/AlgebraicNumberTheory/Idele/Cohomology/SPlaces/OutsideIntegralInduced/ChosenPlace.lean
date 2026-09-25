/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlock
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.Decomposition
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.EquivariantEquiv
/-!
# Integral induced blocks at the chosen finite place

This file specializes the integral induced-block construction to the actual
chosen localization above a finite place and proves its unramified Tate
cohomology consequences.
-/

@[expose] public section

open scoped NumberField TensorProduct ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

variable
    {K : Type} {L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section ChosenFinitePlace

omit [NumberField L] in
private noncomputable def chosenFinitePlaceDecompositionGroupEquivProvider
    (w₀ : HeightOneSpectrum (𝓞 K)) :=
  decompositionGroupEquivAlgebraicLocalizationAut
    (HeightOneSpectrum.adicAbv K w₀)
    (RayClass.adicAbv_isNontrivial w₀)
    (chosenFinitePlaceExtension (L := L) w₀)

omit [NumberField L] in
@[implicit_reducible]
private noncomputable def
    chosenFinitePlaceLocalizedIntegerUnitsGaloisActionProvider
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction
      (Gal(ChosenFinitePlaceLocalizedCompletion (K := K) (L := L)
        w₀/ChosenFinitePlaceBaseCompletion (K := K) w₀))
      𝒪[ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀]ˣ :=
  galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure
    (ChosenFinitePlaceBaseCompletion (K := K) w₀)
    (ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) w₀)

omit [NumberField L] in
@[implicit_reducible]
private noncomputable def chosenFinitePlaceDecompositionGroupFintypeProvider
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    Fintype
      (absoluteValueDecompositionGroup K
        (chosenFinitePlaceExtension (L := L) w₀).1) :=
  Fintype.ofFinite _

private theorem zpowers_generator_map
    {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    ∀ y : H, y ∈ Subgroup.zpowers (e g) := by
  intro y
  have hmem : e.symm y ∈ Subgroup.zpowers g :=
    hg (e.symm y)
  have himage : e (e.symm y) ∈
      (Subgroup.zpowers g).map e.toMonoidHom :=
    ⟨e.symm y, hmem, rfl⟩
  rw [MonoidHom.map_zpowers] at himage
  simpa using himage

private theorem subsingleton_of_equiv_of_equiv
    {A B C : Type*}
    (eAB : A ≃ B) (eBC : B ≃ C)
    (hC : Subsingleton C) :
    Subsingleton A :=
  ⟨fun _ _ ↦
    eAB.injective
      (eBC.injective (@Subsingleton.elim C hC _ _))⟩

/-- Forget multiplication using the dictionaries already present in the equivalence. -/
private def underlyingEquivOfMulEquiv
    {A B : Type*} {mulA : Mul A} {mulB : Mul B}
    (e : @MulEquiv A B mulA mulB) : A ≃ B :=
  e.toEquiv

private theorem apply_of_zpowers_generator_map
    {G H : Type*} [Group G] [Group H]
    {P : H → Prop}
    (e : G ≃* H) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hP : ∀ h : H,
      (∀ y : H, y ∈ Subgroup.zpowers h) → P h) :
    P (e g) :=
  hP (e g) (zpowers_generator_map e g hg)

private theorem herbrandH0_subsingleton_of_action_and_group_equiv
    {G H A X : Type*}
    [Group G] [Fintype G] [Group H] [Fintype H]
    [CommGroup A] [MulDistribMulAction H A] [Mul X]
    (eGroup : G ≃* H)
    (eAction :
      X ≃*
        letI : MulDistribMulAction G A :=
          MulDistribMulAction.compHom A eGroup.toMonoidHom
        HerbrandH0 G A)
    (hH : Subsingleton (HerbrandH0 H A)) :
    Subsingleton X := by
  let : MulDistribMulAction G A :=
    MulDistribMulAction.compHom A eGroup.toMonoidHom
  let eChange :=
    herbrandH0CompMulEquiv (A := A) eGroup
  exact subsingleton_of_equiv_of_equiv
    eAction.toEquiv eChange.toEquiv hH

private theorem herbrandHMinusOne_subsingleton_of_action_and_group_equiv
    {G H A X : Type*}
    [Group G] [Fintype G] [Group H] [Fintype H]
    [CommGroup A] [MulDistribMulAction H A] [Mul X]
    (eGroup : G ≃* H) (g : G)
    (eAction :
      X ≃*
        letI : MulDistribMulAction G A :=
          MulDistribMulAction.compHom A eGroup.toMonoidHom
        HerbrandHMinusOne G A g)
    (hH : Subsingleton
      (HerbrandHMinusOne H A (eGroup g))) :
    Subsingleton X := by
  let : MulDistribMulAction G A :=
    MulDistribMulAction.compHom A eGroup.toMonoidHom
  let eChange :=
    herbrandHMinusOneCompMulEquiv
      (A := A) eGroup g
  exact subsingleton_of_equiv_of_equiv
    eAction.toEquiv eChange.toEquiv hH

omit [NumberField L] in
private theorem
    chosenFinitePlaceDecompositionGroupIntegerUnits_unramifiedHerbrand_subsingleton
    (w₀ : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hunram : ChosenFinitePlaceIsUnramified
      (K := K) (L := L) w₀) :
    let E := ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) w₀
    let H := absoluteValueDecompositionGroup K
      (chosenFinitePlaceExtension (L := L) w₀).1
    letI : Fintype H :=
      chosenFinitePlaceDecompositionGroupFintypeProvider
        (K := K) (L := L) w₀
    letI : MulDistribMulAction H 𝒪[E]ˣ :=
      chosenFinitePlaceDecompositionGroupIntegerUnitsAction
        (K := K) (L := L) w₀
    Subsingleton (HerbrandH0 H 𝒪[E]ˣ) ∧
      Subsingleton
        (HerbrandHMinusOne H 𝒪[E]ˣ
          (subgroupGeneratorOfGenerator H σ hσ)) := by
  let vK := HeightOneSpectrum.adicAbv K w₀
  let w := chosenFinitePlaceExtension (L := L) w₀
  let E := ChosenFinitePlaceLocalizedCompletion
    (K := K) (L := L) w₀
  let H := absoluteValueDecompositionGroup K w.1
  let eLocal :=
    chosenFinitePlaceDecompositionGroupEquivProvider
      (K := K) (L := L) w₀
  let : MulDistribMulAction
      (Gal(E/vK.Completion)) 𝒪[E]ˣ :=
    chosenFinitePlaceLocalizedIntegerUnitsGaloisActionProvider
      (K := K) (L := L) w₀
  let : Fintype H :=
    chosenFinitePlaceDecompositionGroupFintypeProvider
      (K := K) (L := L) w₀
  let : MulDistribMulAction H 𝒪[E]ˣ :=
    chosenFinitePlaceDecompositionGroupIntegerUnitsAction
      (K := K) (L := L) w₀
  let δ := subgroupGeneratorOfGenerator H σ hσ
  have hlocal :=
    apply_of_zpowers_generator_map eLocal δ
      (subgroupGeneratorOfGenerator_generates H σ hσ)
      (fun g hg ↦
        chosenFinitePlaceLocalizedIntegerUnits_unramifiedHerbrand_subsingleton
          (K := K) (L := L) w₀ g hg hunram)
  have hsmul :
      ∀ (h : H) (x : 𝒪[E]ˣ),
        (MulEquiv.refl 𝒪[E]ˣ)
            ((chosenFinitePlaceDecompositionGroupIntegerUnitsAction
              (K := K) (L := L) w₀).smul h x) =
          (MulDistribMulAction.compHom
            𝒪[E]ˣ eLocal.toMonoidHom).smul h
              ((MulEquiv.refl 𝒪[E]ˣ) x) := by
    intro h x
    exact
      chosenFinitePlaceDecompositionGroupIntegerUnitsAction_smul_eq_pullback
        (K := K) (L := L) w₀ h x
  let eActionH0 :=
    @herbrandH0EquivariantMulEquiv
      H 𝒪[E]ˣ 𝒪[E]ˣ _ _ _ _
      (chosenFinitePlaceDecompositionGroupIntegerUnitsAction
        (K := K) (L := L) w₀)
      (MulDistribMulAction.compHom 𝒪[E]ˣ eLocal.toMonoidHom)
      (MulEquiv.refl 𝒪[E]ˣ) hsmul
  let eActionHMinusOne :=
    @herbrandHMinusOneEquivariantMulEquiv
      H 𝒪[E]ˣ 𝒪[E]ˣ _ _ _ _
      (chosenFinitePlaceDecompositionGroupIntegerUnitsAction
        (K := K) (L := L) w₀)
      (MulDistribMulAction.compHom 𝒪[E]ˣ eLocal.toMonoidHom)
      (MulEquiv.refl 𝒪[E]ˣ) hsmul δ
  let eGroupH0 := herbrandH0CompMulEquiv (A := 𝒪[E]ˣ) eLocal
  let eGroupHMinusOne :=
    herbrandHMinusOneCompMulEquiv (A := 𝒪[E]ˣ) eLocal δ
  exact
    ⟨subsingleton_of_equiv_of_equiv
        (underlyingEquivOfMulEquiv eActionH0)
        (underlyingEquivOfMulEquiv eGroupH0) hlocal.1,
      subsingleton_of_equiv_of_equiv
        (underlyingEquivOfMulEquiv eActionHMinusOne)
        (underlyingEquivOfMulEquiv eGroupHMinusOne) hlocal.2⟩

omit [NumberField L] in
/-- At an unramified chosen finite extension, the actual integral tensor
subgroup has trivial degree-zero Herbrand cohomology. -/
theorem
    relativeLocalTensorDecompositionIntegralUnitSubgroup_unramifiedHerbrandH0_subsingleton
    (w₀ : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hunram : ChosenFinitePlaceIsUnramified
      (K := K) (L := L) w₀) :
    letI :=
      relativeLocalTensorDecompositionIntegralUnitSubgroupAction
        (K := K) (L := L) w₀
    Subsingleton
      (HerbrandH0 (L ≃ₐ[K] L)
        (relativeLocalTensorDecompositionIntegralUnitSubgroup
          (K := K) (L := L) w₀)) := by
  let :=
    relativeLocalTensorDecompositionIntegralUnitSubgroupAction
      (K := K) (L := L) w₀
  let E := ChosenFinitePlaceLocalizedCompletion
    (K := K) (L := L) w₀
  let H := absoluteValueDecompositionGroup K
    (chosenFinitePlaceExtension (L := L) w₀).1
  let : Fintype H :=
    chosenFinitePlaceDecompositionGroupFintypeProvider
      (K := K) (L := L) w₀
  let : MulDistribMulAction H 𝒪[E]ˣ :=
    chosenFinitePlaceDecompositionGroupIntegerUnitsAction
      (K := K) (L := L) w₀
  have hdecomp :=
    chosenFinitePlaceDecompositionGroupIntegerUnits_unramifiedHerbrand_subsingleton
      (K := K) (L := L) w₀ σ hσ hunram
  let eTensor := herbrandH0EquivariantMulEquiv
    (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits
      (K := K) (L := L) w₀)
    (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits_smul
      (K := K) (L := L) w₀)
  let eShapiro :=
    inducedHerbrandH0EquivOfFiniteCyclic (B := 𝒪[E]ˣ) H σ hσ
  refine ⟨fun x y ↦ eTensor.injective ?_⟩
  refine eShapiro.injective ?_
  exact @Subsingleton.elim _ hdecomp.1 _ _

omit [NumberField L] in
/-- At an unramified chosen finite extension, the actual integral tensor
subgroup has trivial degree-minus-one Herbrand cohomology. -/
theorem
    relativeLocalTensorDecompositionIntegralUnitSubgroup_unramifiedHerbrandHMinusOne_subsingleton
    (w₀ : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hunram : ChosenFinitePlaceIsUnramified
      (K := K) (L := L) w₀) :
    letI :=
      relativeLocalTensorDecompositionIntegralUnitSubgroupAction
        (K := K) (L := L) w₀
    Subsingleton
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (relativeLocalTensorDecompositionIntegralUnitSubgroup
          (K := K) (L := L) w₀) σ) := by
  let :=
    relativeLocalTensorDecompositionIntegralUnitSubgroupAction
      (K := K) (L := L) w₀
  let E := ChosenFinitePlaceLocalizedCompletion
    (K := K) (L := L) w₀
  let H := absoluteValueDecompositionGroup K
    (chosenFinitePlaceExtension (L := L) w₀).1
  let : Fintype H :=
    chosenFinitePlaceDecompositionGroupFintypeProvider
      (K := K) (L := L) w₀
  let : MulDistribMulAction H 𝒪[E]ˣ :=
    chosenFinitePlaceDecompositionGroupIntegerUnitsAction
      (K := K) (L := L) w₀
  let δ := subgroupGeneratorOfGenerator H σ hσ
  have hdecomp :=
    chosenFinitePlaceDecompositionGroupIntegerUnits_unramifiedHerbrand_subsingleton
      (K := K) (L := L) w₀ σ hσ hunram
  let eTensor := herbrandHMinusOneEquivariantMulEquiv
    (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits
      (K := K) (L := L) w₀)
    (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits_smul
      (K := K) (L := L) w₀)
    σ
  let eShapiro :=
    inducedHerbrandHMinusOneEquivOfFiniteCyclic (B := 𝒪[E]ˣ) H σ hσ
  refine ⟨fun x y ↦ eTensor.injective ?_⟩
  refine eShapiro.injective ?_
  exact @Subsingleton.elim _ hdecomp.2 _ _

end ChosenFinitePlace
