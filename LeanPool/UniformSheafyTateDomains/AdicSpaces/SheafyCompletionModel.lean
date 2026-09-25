/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.SheafyRingEquivTransport
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.CompletionModelIndependence
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.PresheafIdentification

/-!
# The clean complete-ring/completion-model equivalence and model independence

**C0.** For a *complete* Huber ring `A` (no Tate, no noetherian hypotheses), the
canonical map into any completion model is a bicontinuous ring equivalence:

* `completeRingEquivCompletionModel (P) : A ≃+* CompletionModel A P`, whose
  forward map is literally `(globalLocData P).canonicalMap`
  (`completeRingEquivCompletionModel_apply`), with
  `completeRingEquivCompletionModel_continuous` and `_symm_continuous`.

The inverse is the completion-extension of the away-one collapse
`Localization.Away 1 →+* A` (the `IsLocalization.Away.lift` of the identity),
which is continuous for the localization topology by
`locTopology_continuous_lift` (the only generator is `1`, whose image is
power-bounded).

This replaces any use of the overscoped `globalSections_equiv` (which leaks
`PlusSubring`, `DecidableEq`, noetherian and restriction-lift hypotheses and is
unusable for the finite-jet ring).

**C1.** Completion-model independence of ring-level sheafiness, for a Tate
ring `A` (no completeness of `A`, no plus rings, no noetherian hypotheses):

* `isSheafyTateRing_iff_for_completionModel` — checking one completion model is
  equivalent to checking every completion model;
* `isSheafyTateRing_iff_exists_completionModel` — the existential form;
* `isSheafyTateRing_iff_isSheafyComplete` — for *complete* Tate `A`, the
  ring-level Definition 8.26 collapses to `IsSheafyComplete A` through the C0
  equivalence.

Only bicontinuity of `completionModelCompare` is used — canonical-map
compatibility is not needed for the sheafiness transport.
-/

@[expose] public section

noncomputable section

namespace ValuationSpectrum

universe u

section C0

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [IsHuberRing A] [T2Space A] [NonarchimedeanRing A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]

/-- The away-one collapse `Localization.Away 1 →+* A`: the `IsLocalization` lift
of the identity along the (unit) image of `1`. -/
private noncomputable def completeRingCollapseAlg (P : PairOfDefinition A) :
    Localization.Away ((globalLocData P).s) →+* A :=
  IsLocalization.Away.lift (globalLocData P).s
    (isUnit_one.map (RingHom.id A) : IsUnit ((RingHom.id A) (1 : A)))

omit [T2Space A] [NonarchimedeanRing A] 
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] in
/-- The collapse tracks the algebra map. -/
private theorem completeRingCollapseAlg_algebraMap (P : PairOfDefinition A) (a : A) :
    completeRingCollapseAlg P
      (algebraMap A (Localization.Away ((globalLocData P).s)) a) = a :=
  IsLocalization.Away.lift_eq (g := RingHom.id A) _ _ a

omit [T2Space A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] in
/-- Continuity of the collapse for the whole-space localization topology: the
generator set is `{1}`, whose image is power-bounded. -/
private theorem completeRingCollapseAlg_continuous (P : PairOfDefinition A) :
    @Continuous _ _ (globalLocData P).topology _ (completeRingCollapseAlg P) := by
  refine locTopology_continuous_lift P ({1} : Finset A) (1 : A)
    (globalLocData P).hopen (completeRingCollapseAlg P) ?_ ?_
  · exact continuous_id.congr
      fun a => (completeRingCollapseAlg_algebraMap P a).symm
  · intro t ht
    rw [Finset.mem_singleton] at ht
    subst ht
    have hdiv : divByS (1 : A) (1 : A) = 1 := by
      rw [show divByS (1 : A) (1 : A) =
          IsLocalization.mk' (Localization.Away (1 : A)) (1 : A)
            (1 : Submonoid.powers (1 : A)) from rfl,
        IsLocalization.mk'_one, map_one]
    rw [hdiv]
    exact (map_one (completeRingCollapseAlg P)).symm ▸
      TopologicalRing.isPowerBounded_one

/-- The inverse map: the completion-extension of the away-one collapse. -/
private noncomputable def completeRingCompletionModelInv (P : PairOfDefinition A) :
    CompletionModel A P →+* A := by
  letI : UniformSpace (Localization.Away ((globalLocData P).s)) :=
    (globalLocData P).uniformSpace
  letI : IsTopologicalRing (Localization.Away ((globalLocData P).s)) :=
    (globalLocData P).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away ((globalLocData P).s)) :=
    (globalLocData P).isUniformAddGroup
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  haveI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  exact UniformSpace.Completion.extensionHom (completeRingCollapseAlg P)
    (completeRingCollapseAlg_continuous P)

/-- The inverse on the dense localization image is the collapse. -/
private theorem completeRingCompletionModelInv_coe (P : PairOfDefinition A)
    (l : Localization.Away ((globalLocData P).s)) :
    completeRingCompletionModelInv P ((globalLocData P).coeRingHom l) =
      completeRingCollapseAlg P l := by
  letI : UniformSpace (Localization.Away ((globalLocData P).s)) :=
    (globalLocData P).uniformSpace
  letI : IsTopologicalRing (Localization.Away ((globalLocData P).s)) :=
    (globalLocData P).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away ((globalLocData P).s)) :=
    (globalLocData P).isUniformAddGroup
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  haveI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  exact UniformSpace.Completion.extensionHom_coe _ _ l

/-- Backward-after-canonical is the identity. -/
private theorem completeRingCompletionModelInv_canonicalMap (P : PairOfDefinition A)
    (a : A) :
    completeRingCompletionModelInv P ((globalLocData P).canonicalMap a) = a := by
  rw [show (globalLocData P).canonicalMap a = (globalLocData P).coeRingHom
      (algebraMap A (Localization.Away ((globalLocData P).s)) a) from rfl,
    completeRingCompletionModelInv_coe, completeRingCollapseAlg_algebraMap]

/-- Canonical-after-backward is the identity (via `UniformSpace.Completion.ext'`
at the literal target `presheafValue (globalLocData P)`). -/
private theorem canonicalMap_completeRingCompletionModelInv (P : PairOfDefinition A)
    (x : presheafValue (globalLocData P)) :
    (globalLocData P).canonicalMap (completeRingCompletionModelInv P x) = x := by
  letI : UniformSpace (Localization.Away ((globalLocData P).s)) :=
    (globalLocData P).uniformSpace
  letI : IsTopologicalRing (Localization.Away ((globalLocData P).s)) :=
    (globalLocData P).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away ((globalLocData P).s)) :=
    (globalLocData P).isUniformAddGroup
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  haveI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  refine @UniformSpace.Completion.ext' _ _ (presheafValue (globalLocData P)) _ _
    (fun y => (globalLocData P).canonicalMap (completeRingCompletionModelInv P y))
    (fun y => y)
    ((canonicalMap_continuous _).comp
      UniformSpace.Completion.continuous_extension)
    continuous_id ?_ x
  intro l
  show (globalLocData P).canonicalMap
    (completeRingCompletionModelInv P ((globalLocData P).coeRingHom l)) =
    (globalLocData P).coeRingHom l
  rw [completeRingCompletionModelInv_coe]
  have hhom : ((globalLocData P).canonicalMap).comp (completeRingCollapseAlg P) =
      (globalLocData P).coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers ((globalLocData P).s)) ?_
    ext a
    simp only [RingHom.comp_apply]
    rw [completeRingCollapseAlg_algebraMap]
    rfl
  exact DFunLike.congr_fun hhom l

/-- **The complete-ring/completion-model equivalence** (C0, Wedhorn Remark 8.3
for complete `A`): the canonical map `A → Â = CompletionModel A P` is a ring
equivalence. Hypotheses: complete Huber only — no Tate, no noetherian, no plus
ring, no `DecidableEq`, no localization-lift package. -/
noncomputable def completeRingEquivCompletionModel (P : PairOfDefinition A) :
    A ≃+* CompletionModel A P :=
  RingEquiv.ofRingHom ((globalLocData P).canonicalMap)
    (completeRingCompletionModelInv P)
    (RingHom.ext fun x => canonicalMap_completeRingCompletionModelInv P x)
    (RingHom.ext fun a => completeRingCompletionModelInv_canonicalMap P a)

@[simp] theorem completeRingEquivCompletionModel_apply (P : PairOfDefinition A)
    (a : A) :
    completeRingEquivCompletionModel P a = (globalLocData P).canonicalMap a := rfl

theorem completeRingEquivCompletionModel_continuous (P : PairOfDefinition A) :
    Continuous (completeRingEquivCompletionModel P) :=
  canonicalMap_continuous (globalLocData P)

theorem completeRingEquivCompletionModel_symm_continuous (P : PairOfDefinition A) :
    Continuous (completeRingEquivCompletionModel P).symm := by
  letI : UniformSpace (Localization.Away ((globalLocData P).s)) :=
    (globalLocData P).uniformSpace
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  haveI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  exact UniformSpace.Completion.continuous_extension

end C0

/-! ### C1: completion-model independence of ring-level sheafiness -/

section C1

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTateRing A]

/-- **Checking one completion model suffices** (C1): ring-level Tate sheafiness
(`IsSheafyTateRing`, which quantifies over *every* completion model) is
equivalent to `IsSheafyComplete` of any *single* completion model. Forward is
specialization; backward transports the fixed model's sheafiness to every other
model along the bicontinuous `completionModelCompare`. No plus-ring, noetherian,
decidable-equality, or localization-lift hypotheses appear. -/
theorem isSheafyTateRing_iff_for_completionModel (P : PairOfDefinition A) :
    IsSheafyTateRing A ↔ IsSheafyComplete (CompletionModel A P) := by
  constructor
  · intro h Bplus
    exact h P Bplus
  · intro h P' Bplus
    exact (isSheafyComplete_congr (completionModelCompare P P')
      (completionModelCompare_continuous P P')
      (completionModelCompare_symm_continuous P P')).mp h Bplus

/-- **The existential form** (C1): ring-level Tate sheafiness is equivalent to
sheafiness of *some* completion model. -/
theorem isSheafyTateRing_iff_exists_completionModel :
    IsSheafyTateRing A ↔
      ∃ P : PairOfDefinition A, IsSheafyComplete (CompletionModel A P) := by
  constructor
  · intro h
    obtain ⟨P⟩ := (‹IsTateRing A›.toIsHuberRing).exists_pairOfDefinition
    exact ⟨P, (isSheafyTateRing_iff_for_completionModel P).mp h⟩
  · rintro ⟨P, hP⟩
    exact (isSheafyTateRing_iff_for_completionModel P).mpr hP

variable [T2Space A] [NonarchimedeanRing A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]

/-- **For complete Tate rings the two ring-level notions coincide** (C1): the
completion-model quantification of Wedhorn Definition 8.26 collapses to
`IsSheafyComplete A` itself, through the C0 equivalence `A ≃+* Â`. -/
theorem isSheafyTateRing_iff_isSheafyComplete :
    IsSheafyTateRing A ↔ IsSheafyComplete A := by
  obtain ⟨P⟩ := (‹IsTateRing A›.toIsHuberRing).exists_pairOfDefinition
  rw [isSheafyTateRing_iff_for_completionModel P]
  exact (isSheafyComplete_congr (completeRingEquivCompletionModel P)
    (completeRingEquivCompletionModel_continuous P)
    (completeRingEquivCompletionModel_symm_continuous P)).symm

end C1

end ValuationSpectrum
