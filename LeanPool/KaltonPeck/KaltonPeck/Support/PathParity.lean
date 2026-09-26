/-
Copyright (c) 2026 Avik Das. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avik Das
-/
module

/-
Copyright (c) 2026 adas1236. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: adas1236
-/
public import LeanPool.KaltonPeck.KaltonPeck.Support.Fredholm
public import LeanPool.KaltonPeck.KaltonPeck.Support.FiniteParity
public import Mathlib.Analysis.Normed.Ring.Units

/-!
# Parity along paths of alternating forms

This file constructs kernel splittings and local Schur reductions and proves the mod-two
invariance result for paths of Fredholm alternating forms.
-/

@[expose] public section

namespace KaltonPeck.Support.PathParity

noncomputable
section

/-- A closed kernel complement, continuous dual coordinates, and the invertible range block.

The continuous equivalence `dualCoordinates` supplies the two continuous coordinate projections.
Blueprint: `lem:kernel-splitting`; audit: `AUX-FREDHOLM-KERNEL-COMPLEMENT` and
`AUX-ANNIHILATOR-DUAL-SPLIT`. -/
structure KernelSplittingData {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (eta : ContinuousAlternatingForm X) where
  kernelFiniteDimensional : FiniteDimensional ℝ eta.radical
  /-- A closed topological complement to the radical. -/
  complement : Submodule ℝ X
  complementClosed : IsClosed (complement : Set X)
  kernel_disjoint_complement : Disjoint eta.radical complement
  kernel_sup_complement : eta.radical ⊔ complement = ⊤
  /-- Continuous coordinates for the dual splitting induced by the complement. -/
  dualCoordinates :
    StrongDual ℝ X ≃L[ℝ]
      (Forms.continuousAnnihilator complement × Forms.continuousAnnihilator eta.radical)
  dualCoordinates_symm_apply
      (p : Forms.continuousAnnihilator complement ×
        Forms.continuousAnnihilator eta.radical) :
    (dualCoordinates.symm p : StrongDual ℝ X) =
      (p.1 : StrongDual ℝ X) + (p.2 : StrongDual ℝ X)
  /-- Restriction identifies the annihilator of the complement with the radical dual. -/
  annihilatorComplementEquivKernelDual :
    Forms.continuousAnnihilator complement ≃L[ℝ] StrongDual ℝ eta.radical
  annihilatorComplementEquivKernelDual_apply
      (phi : Forms.continuousAnnihilator complement) (f : eta.radical) :
    annihilatorComplementEquivKernelDual phi f = (phi : StrongDual ℝ X) (f : X)
  range_eq_annihilator :
    eta.toDual.toLinearMap.range = Forms.continuousAnnihilator eta.radical
  /-- The nondegenerate range block on the chosen complement. -/
  restrictionEquiv : complement ≃L[ℝ] Forms.continuousAnnihilator eta.radical
  restrictionEquiv_apply (y : complement) :
    (restrictionEquiv y : StrongDual ℝ X) = eta.toDual (y : X)

/-- The splitting package at a Fredholm alternating operator.

Blueprint: `lem:kernel-splitting`. -/
def kernelSplitting {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (eta : ContinuousAlternatingForm X)
    (hReflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X))
    (hFredholm : IsFredholm eta.toDual) : KernelSplittingData eta := by
  have hRange := Fredholm.alternatingFredholmRange eta hReflexive hFredholm
  letI : FiniteDimensional ℝ eta.radical := hFredholm.1
  let hComplemented :=
    Submodule.ClosedComplemented.of_finiteDimensional eta.radical
  let Y : Submodule ℝ X := hComplemented.complement
  let hTop : Submodule.IsTopCompl eta.radical Y :=
    hComplemented.isTopCompl_complement
  letI : CompleteSpace Y :=
    hComplemented.isClosed_complement.completeSpace_coe
  let pF : X →L[ℝ] eta.radical :=
    eta.radical.projectionOntoL Y hTop
  let pY : X →L[ℝ] Y :=
    Y.projectionOntoL eta.radical hTop.symm
  have hProj (x : X) : (pF x : X) + (pY x : X) = x := by
    exact Submodule.projectionL_add_projectionL_eq_self hTop x
  let rF : StrongDual ℝ X →L[ℝ] StrongDual ℝ eta.radical :=
    (ContinuousLinearMap.compL ℝ eta.radical X ℝ).flip eta.radical.subtypeL
  let rY : StrongDual ℝ X →L[ℝ] StrongDual ℝ Y :=
    (ContinuousLinearMap.compL ℝ Y X ℝ).flip Y.subtypeL
  let lF : StrongDual ℝ eta.radical →L[ℝ] StrongDual ℝ X :=
    (ContinuousLinearMap.compL ℝ X eta.radical ℝ).flip pF
  let lY : StrongDual ℝ Y →L[ℝ] StrongDual ℝ X :=
    (ContinuousLinearMap.compL ℝ X Y ℝ).flip pY
  let lFA : StrongDual ℝ eta.radical →L[ℝ]
      Forms.continuousAnnihilator Y :=
    lF.codRestrict (Forms.continuousAnnihilator Y) (fun a => by
      change rY (lF a) = 0
      apply ContinuousLinearMap.ext
      intro y
      change a (pF (y : X)) = 0
      simp [pF])
  let lYA : StrongDual ℝ Y →L[ℝ]
      Forms.continuousAnnihilator eta.radical :=
    lY.codRestrict (Forms.continuousAnnihilator eta.radical) (fun a => by
      change rF (lY a) = 0
      apply ContinuousLinearMap.ext
      intro f
      change a (pY (f : X)) = 0
      simp [pY])
  let annYToF : Forms.continuousAnnihilator Y →L[ℝ]
      StrongDual ℝ eta.radical :=
    rF.comp (Forms.continuousAnnihilator Y).subtypeL
  let annYLinearEquiv :
      Forms.continuousAnnihilator Y ≃ₗ[ℝ] StrongDual ℝ eta.radical :=
    { toFun := annYToF
      invFun := lFA
      left_inv := by
        intro a
        apply Subtype.ext
        apply ContinuousLinearMap.ext
        intro x
        have haY : (a : StrongDual ℝ X) (pY x : X) = 0 := by
          have ha := a.property
          change rY (a : StrongDual ℝ X) = 0 at ha
          exact DFunLike.congr_fun ha (pY x)
        change (a : StrongDual ℝ X) (pF x : X) =
          (a : StrongDual ℝ X) x
        calc
          (a : StrongDual ℝ X) (pF x : X) =
              (a : StrongDual ℝ X) (pF x : X) +
                (a : StrongDual ℝ X) (pY x : X) := by rw [haY, add_zero]
          _ = (a : StrongDual ℝ X) ((pF x : X) + (pY x : X)) := by
            rw [map_add]
          _ = (a : StrongDual ℝ X) x :=
            congrArg (a : StrongDual ℝ X) (hProj x)
      right_inv := by
        intro a
        apply ContinuousLinearMap.ext
        intro f
        change a (pF (f : X)) = a f
        simp [pF]
      map_add' := annYToF.map_add
      map_smul' := annYToF.map_smul }
  let annYEquivF :
      Forms.continuousAnnihilator Y ≃L[ℝ] StrongDual ℝ eta.radical :=
    ContinuousLinearEquiv.mk annYLinearEquiv annYToF.continuous lFA.continuous
  let coordF : StrongDual ℝ X →L[ℝ] Forms.continuousAnnihilator Y :=
    lFA.comp rF
  let coordY : StrongDual ℝ X →L[ℝ]
      Forms.continuousAnnihilator eta.radical :=
    lYA.comp rY
  let coordinates : StrongDual ℝ X →L[ℝ]
      (Forms.continuousAnnihilator Y ×
        Forms.continuousAnnihilator eta.radical) :=
    coordF.prod coordY
  let sumCoordinates :
      (Forms.continuousAnnihilator Y ×
        Forms.continuousAnnihilator eta.radical) →L[ℝ] StrongDual ℝ X :=
    (Forms.continuousAnnihilator Y).subtypeL.coprod
      (Forms.continuousAnnihilator eta.radical).subtypeL
  let dualLinearEquiv :
      StrongDual ℝ X ≃ₗ[ℝ]
        (Forms.continuousAnnihilator Y ×
          Forms.continuousAnnihilator eta.radical) :=
    { toFun := coordinates
      invFun := sumCoordinates
      left_inv := by
        intro phi
        apply ContinuousLinearMap.ext
        intro x
        change phi (pF x : X) + phi (pY x : X) = phi x
        rw [← map_add, hProj]
      right_inv := by
        rintro ⟨a, b⟩
        apply Prod.ext
        · have hbF : rF (b : StrongDual ℝ X) = 0 := b.property
          change lFA (rF ((a : StrongDual ℝ X) + (b : StrongDual ℝ X))) = a
          rw [map_add, hbF, add_zero]
          exact annYLinearEquiv.left_inv a
        · have haY : rY (a : StrongDual ℝ X) = 0 := a.property
          change lYA (rY ((a : StrongDual ℝ X) + (b : StrongDual ℝ X))) = b
          rw [map_add, haY, zero_add]
          apply Subtype.ext
          apply ContinuousLinearMap.ext
          intro x
          have hbF : (b : StrongDual ℝ X) (pF x : X) = 0 := by
            have hb := b.property
            change rF (b : StrongDual ℝ X) = 0 at hb
            exact DFunLike.congr_fun hb (pF x)
          change (b : StrongDual ℝ X) (pY x : X) =
            (b : StrongDual ℝ X) x
          calc
            (b : StrongDual ℝ X) (pY x : X) =
                (b : StrongDual ℝ X) (pF x : X) +
                  (b : StrongDual ℝ X) (pY x : X) := by rw [hbF, zero_add]
            _ = (b : StrongDual ℝ X) ((pF x : X) + (pY x : X)) := by
              rw [map_add]
            _ = (b : StrongDual ℝ X) x :=
              congrArg (b : StrongDual ℝ X) (hProj x)
      map_add' := coordinates.map_add
      map_smul' := coordinates.map_smul }
  let dualEquiv :
      StrongDual ℝ X ≃L[ℝ]
        (Forms.continuousAnnihilator Y ×
          Forms.continuousAnnihilator eta.radical) :=
    ContinuousLinearEquiv.mk dualLinearEquiv coordinates.continuous
      sumCoordinates.continuous
  have hRadical (f : eta.radical) : eta.toDual (f : X) = 0 := f.property
  let SY : Y →L[ℝ] StrongDual ℝ X := eta.toDual.comp Y.subtypeL
  have hSY_injective : Function.Injective SY := by
    intro y z hyz
    apply Subtype.ext
    have hzero : eta.toDual ((y - z : Y) : X) = 0 := by
      simpa [SY, sub_eq_zero] using sub_eq_zero.mpr hyz
    have hzmem : ((y - z : Y) : X) ∈ (⊥ : Submodule ℝ X) :=
      hTop.isCompl.disjoint.le_bot ⟨hzero, (y - z).property⟩
    exact (Submodule.mem_bot ℝ).mp hzmem |> sub_eq_zero.mp
  have hSY_range : SY.toLinearMap.range = eta.toDual.toLinearMap.range := by
    apply le_antisymm
    · rintro phi ⟨y, rfl⟩
      exact ⟨(y : X), rfl⟩
    · rintro phi ⟨x, rfl⟩
      refine ⟨pY x, ?_⟩
      change eta.toDual (pY x : X) = eta.toDual x
      calc
        eta.toDual (pY x : X) =
            eta.toDual ((pF x : X) + (pY x : X)) := by
              rw [map_add, hRadical, zero_add]
        _ = eta.toDual x := congrArg eta.toDual (hProj x)
  have hSY_closed : IsClosed (Set.range SY) := by
    change IsClosed (SY.toLinearMap.range : Set (StrongDual ℝ X))
    rw [hSY_range]
    exact hFredholm.2.1
  let eRange : Y ≃L[ℝ] SY.toLinearMap.range :=
    ContinuousLinearMap.equivRange hSY_injective hSY_closed
  let hSYAnn : SY.toLinearMap.range =
      Forms.continuousAnnihilator eta.radical := hSY_range.trans hRange
  let restrictionEquiv :
      Y ≃L[ℝ] Forms.continuousAnnihilator eta.radical :=
    eRange.trans (ContinuousLinearEquiv.ofEq SY.toLinearMap.range
      (Forms.continuousAnnihilator eta.radical) hSYAnn)
  refine
    { kernelFiniteDimensional := inferInstance
      complement := Y
      complementClosed := hComplemented.isClosed_complement
      kernel_disjoint_complement := hTop.isCompl.disjoint
      kernel_sup_complement := hTop.isCompl.sup_eq_top
      dualCoordinates := dualEquiv
      dualCoordinates_symm_apply := ?_
      annihilatorComplementEquivKernelDual := annYEquivF
      annihilatorComplementEquivKernelDual_apply := ?_
      range_eq_annihilator := hRange
      restrictionEquiv := restrictionEquiv
      restrictionEquiv_apply := ?_ }
  · intro p
    change sumCoordinates p =
      (p.1 : StrongDual ℝ X) + (p.2 : StrongDual ℝ X)
    rfl
  · intro a f
    change (a : StrongDual ℝ X) (f : X) = (a : StrongDual ℝ X) (f : X)
    rfl
  · intro y
    change ((eRange y : SY.toLinearMap.range) : StrongDual ℝ X) =
      eta.toDual (y : X)
    have heRange : eRange y = SY.rangeRestrict y :=
      congrFun (ContinuousLinearMap.coe_equivRange hSY_injective hSY_closed) y
    rw [heRange]
    rfl

/-- The local kernel parametrization and reduced alternating form at one nearby parameter. -/
structure LocalSchurPointData {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (eta0 eta : ContinuousAlternatingForm X) where
  /-- The bounded injection parametrizing the nearby kernel from the fixed kernel. -/
  kernelMap : eta0.radical →L[ℝ] X
  kernelMap_injective : Function.Injective kernelMap
  /-- The finite-dimensional alternating Schur complement on the fixed kernel. -/
  reducedForm : ContinuousAlternatingForm eta0.radical
  reducedForm_apply (f g : eta0.radical) :
    reducedForm.toDual f g = eta.toDual (kernelMap f) (kernelMap g)
  /-- The reduced radical is linearly equivalent to the moving kernel. -/
  radicalEquivKernel : reducedForm.radical ≃ₗ[ℝ] eta.radical
  radicalEquivKernel_apply (f : reducedForm.radical) :
    ((radicalEquivKernel f : eta.radical) : X) = kernelMap (f : eta0.radical)

/-- A continuous operator family remains equivalent near a member that is an equivalence. -/
private theorem exists_nearby_equiv {J Y B : Type*} [MetricSpace J]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (D : J → Y →L[ℝ] B) (hD : Continuous D) (t0 : J) (e : Y ≃L[ℝ] B)
    (hD0 : D t0 = e.toContinuousLinearMap) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ t, dist t t0 < epsilon →
      ∃ e' : Y ≃L[ℝ] B, e'.toContinuousLinearMap = D t := by
  let post : (Y →L[ℝ] B) →L[ℝ] Y →L[ℝ] Y :=
    ContinuousLinearMap.compL ℝ Y B Y e.symm.toContinuousLinearMap
  let P (t : J) : Y →L[ℝ] Y := post (D t)
  have hP_apply (t : J) (y : Y) : P t y = e.symm (D t y) := rfl
  have hP0 : P t0 = ContinuousLinearMap.id ℝ Y := by
    ext y
    rw [hP_apply, hD0]
    exact e.symm_apply_apply y
  have hPContinuous : Continuous P := post.continuous.comp hD
  have hNhd : P ⁻¹' Metric.ball (ContinuousLinearMap.id ℝ Y) 1 ∈ nhds t0 := by
    apply (Metric.isOpen_ball.preimage hPContinuous).mem_nhds
    simp [hP0]
  obtain ⟨epsilon, hEpsilon, hBall⟩ := Metric.mem_nhds_iff.mp hNhd
  refine ⟨epsilon, hEpsilon, ?_⟩
  intro t ht
  have hPtBall := hBall ht
  have hPerturb : ‖ContinuousLinearMap.id ℝ Y - P t‖ < 1 := by
    change dist (P t) (ContinuousLinearMap.id ℝ Y) < 1 at hPtBall
    have hdist : dist (ContinuousLinearMap.id ℝ Y) (P t) < 1 := by
      rwa [dist_comm]
    rwa [dist_eq_norm] at hdist
  let u : (Y →L[ℝ] Y)ˣ := Units.oneSub (ContinuousLinearMap.id ℝ Y - P t) hPerturb
  let PtEquiv : Y ≃L[ℝ] Y := ContinuousLinearEquiv.unitsEquiv ℝ Y u
  have hPtEquiv : PtEquiv.toContinuousLinearMap = P t := by
    ext y
    change (u : Y →L[ℝ] Y) y = P t y
    dsimp only [u]
    rw [Units.val_oneSub]
    simp
  refine ⟨PtEquiv.trans e, ?_⟩
  ext y
  change e (PtEquiv y) = D t y
  have hy := congrArg (fun T : Y →L[ℝ] Y => T y) hPtEquiv
  calc
    e (PtEquiv y) = e (P t y) := congrArg e hy
    _ = D t y := by
      rw [hP_apply]
      exact e.apply_symm_apply (D t y)

/-- Local Schur reduction relative to an arbitrary real parameter set.

For all sufficiently close `t` in `J`, the bounded injection from the fixed kernel restricts to
the displayed linear equivalence from the reduced radical to the moving kernel.
Blueprint: `lem:schur-reduction`; audit: `AUX-LOWER-BLOCK-INVERTIBLE`,
`AUX-SCHUR-KERNEL-PARAMETRIZATION`, `AUX-REDUCED-ALTERNATING-FORM`, and
`AUX-REDUCED-RADICAL-KERNEL`. -/
theorem localSchurReduction {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (J : Set ℝ) (t0 : J) (eta : J → ContinuousAlternatingForm X)
    (hContinuous : Continuous fun t ↦ (eta t).toDual)
    (hReflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X))
    (hFredholm : IsFredholm (eta t0).toDual) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ t : J, |(t : ℝ) - (t0 : ℝ)| < epsilon →
      Nonempty (LocalSchurPointData (eta t0) (eta t)) := by
  let data := kernelSplitting (eta t0) hReflexive hFredholm
  let Y := data.complement
  let A := Forms.continuousAnnihilator Y
  let B := Forms.continuousAnnihilator (eta t0).radical
  let : CompleteSpace Y := data.complementClosed.completeSpace_coe
  let q : StrongDual ℝ X →L[ℝ] B :=
    (ContinuousLinearMap.snd ℝ A B).comp data.dualCoordinates.toContinuousLinearMap
  let C (t : J) : (eta t0).radical →L[ℝ] B :=
    q.comp ((eta t).toDual.comp (eta t0).radical.subtypeL)
  let D (t : J) : Y →L[ℝ] B :=
    q.comp ((eta t).toDual.comp Y.subtypeL)
  have hSecondCoordinate (phi : B) :
      (data.dualCoordinates (phi : StrongDual ℝ X)).2 = phi := by
    have hcoords : data.dualCoordinates (phi : StrongDual ℝ X) = (0, phi) := by
      apply data.dualCoordinates.symm.injective
      rw [data.dualCoordinates.symm_apply_apply, data.dualCoordinates_symm_apply]
      simp
    exact congrArg Prod.snd hcoords
  have hDecompose (phi : StrongDual ℝ X) :
      phi = ((data.dualCoordinates phi).1 : StrongDual ℝ X) +
        ((data.dualCoordinates phi).2 : StrongDual ℝ X) := by
    rw [← data.dualCoordinates_symm_apply (data.dualCoordinates phi),
      data.dualCoordinates.symm_apply_apply]
  have hD0 : D t0 = data.restrictionEquiv.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro y
    change (data.dualCoordinates ((eta t0).toDual (y : X))).2 =
      data.restrictionEquiv y
    rw [← data.restrictionEquiv_apply]
    exact hSecondCoordinate (data.restrictionEquiv y)
  let : NormedAddCommGroup B := inferInstance
  let : NormedSpace ℝ B := inferInstance
  have hDContinuous : Continuous D :=
    ((ContinuousLinearMap.compL ℝ Y (StrongDual ℝ X) B q).comp
      ((ContinuousLinearMap.compL ℝ Y X (StrongDual ℝ X)).flip Y.subtypeL)).continuous.comp
        hContinuous
  obtain ⟨epsilon, hEpsilon, hEquiv⟩ :=
    exists_nearby_equiv D hDContinuous t0 data.restrictionEquiv hD0
  refine ⟨epsilon, hEpsilon, ?_⟩
  intro t ht
  have htDist : dist t t0 < epsilon := by
    simpa [Subtype.dist_eq, Real.dist_eq] using ht
  obtain ⟨DtEquiv, hDtEquiv⟩ := hEquiv t htDist
  let L : (eta t0).radical →L[ℝ] Y :=
    DtEquiv.symm.toContinuousLinearMap.comp (C t)
  have hDL (f : (eta t0).radical) : D t (L f) = C t f := by
    rw [← hDtEquiv]
    exact DtEquiv.apply_symm_apply (C t f)
  let m : (eta t0).radical →L[ℝ] X :=
    (eta t0).radical.subtypeL - Y.subtypeL.comp L
  have hm_apply (f : (eta t0).radical) :
      m f = (f : X) - (L f : X) := rfl
  have hLower (f : (eta t0).radical) :
      q ((eta t).toDual (m f)) = 0 := by
    rw [hm_apply, map_sub, map_sub]
    change C t f - D t (L f) = 0
    rw [hDL]
    exact sub_self (C t f)
  have hmInjective : Function.Injective m := by
    intro f g hfg
    have hzero : m (f - g) = 0 := by
      rw [map_sub, hfg, sub_self]
    rw [hm_apply] at hzero
    have heq : ((f - g : (eta t0).radical) : X) = (L (f - g) : X) :=
      sub_eq_zero.mp hzero
    have hbot : ((f - g : (eta t0).radical) : X) ∈ (⊥ : Submodule ℝ X) :=
      data.kernel_disjoint_complement.le_bot
        ⟨(f - g).property, heq ▸ (L (f - g)).property⟩
    apply Subtype.ext
    exact sub_eq_zero.mp ((Submodule.mem_bot ℝ).mp hbot)
  let reduced : ContinuousAlternatingForm (eta t0).radical :=
    { toDual :=
        ((ContinuousLinearMap.flip
          (ContinuousLinearMap.compL ℝ (eta t0).radical X ℝ)) m).comp
            ((eta t).toDual.comp m)
      alternating := fun f => (eta t).alternating (m f) }
  have hReducedApply (f g : (eta t0).radical) :
      reduced.toDual f g = (eta t).toDual (m f) (m g) := rfl
  have hRadicalToKernel (f : reduced.radical) :
      (eta t).toDual (m (f : (eta t0).radical)) = 0 := by
    let phi : StrongDual ℝ X := (eta t).toDual (m (f : (eta t0).radical))
    have hSecond : (data.dualCoordinates phi).2 = 0 := by
      exact hLower f
    have hPhiFirst :
        phi = ((data.dualCoordinates phi).1 : StrongDual ℝ X) := by
      calc
        phi = ((data.dualCoordinates phi).1 : StrongDual ℝ X) +
            ((data.dualCoordinates phi).2 : StrongDual ℝ X) := hDecompose phi
        _ = ((data.dualCoordinates phi).1 : StrongDual ℝ X) := by
          rw [hSecond]
          simp
    have hVanishY (y : Y) : phi (y : X) = 0 := by
      rw [hPhiFirst]
      have hy := (data.dualCoordinates phi).1.property
      change ((ContinuousLinearMap.compL ℝ Y X ℝ).flip Y.subtypeL)
        ((data.dualCoordinates phi).1 : StrongDual ℝ X) = 0 at hy
      exact DFunLike.congr_fun hy y
    have hFirst : (data.dualCoordinates phi).1 = 0 := by
      apply data.annihilatorComplementEquivKernelDual.injective
      apply ContinuousLinearMap.ext
      intro g
      rw [data.annihilatorComplementEquivKernelDual_apply]
      change ((data.dualCoordinates phi).1 : StrongDual ℝ X) (g : X) = 0
      rw [← hPhiFirst]
      calc
        phi (g : X) = phi (m g + (L g : X)) := by
          congr 1
          rw [hm_apply]
          abel
        _ = phi (m g) + phi (L g : X) := map_add _ _ _
        _ = 0 + 0 := by
          congr 1
          · have hf := DFunLike.congr_fun f.property g
            exact hReducedApply f g ▸ hf
          · exact hVanishY (L g)
        _ = 0 := zero_add 0
    calc
      (eta t).toDual (m (f : (eta t0).radical)) = phi := rfl
      _ = ((data.dualCoordinates phi).1 : StrongDual ℝ X) +
          ((data.dualCoordinates phi).2 : StrongDual ℝ X) := hDecompose phi
      _ = 0 := by rw [hFirst, hSecond]; simp
  let toKernel : reduced.radical →ₗ[ℝ] (eta t).radical :=
    { toFun := fun f => ⟨m (f : (eta t0).radical), hRadicalToKernel f⟩
      map_add' := by
        intro f g
        apply Subtype.ext
        exact m.map_add f g
      map_smul' := by
        intro a f
        apply Subtype.ext
        exact m.map_smul a f }
  have hToKernelInjective : Function.Injective toKernel := by
    intro f g hfg
    apply Subtype.ext
    apply hmInjective
    exact congrArg Subtype.val hfg
  have hToKernelSurjective : Function.Surjective toKernel := by
    intro z
    have hzSup : (z : X) ∈ (eta t0).radical ⊔ Y := by
      rw [data.kernel_sup_complement]
      exact Submodule.mem_top
    rcases Submodule.mem_sup.1 hzSup with ⟨x, hx, y, hy, hxy⟩
    let f : (eta t0).radical := ⟨x, hx⟩
    let y' : Y := ⟨y, hy⟩
    have hzAdd : (z : X) = (f : X) + (y' : X) := hxy.symm
    have hzLower : C t f + D t y' = 0 := by
      have hz := congrArg q z.property
      rw [map_zero] at hz
      rw [hzAdd, map_add, map_add] at hz
      exact hz
    have hDsum : D t (L f + y') = 0 := by
      rw [map_add, hDL]
      exact hzLower
    have hsum : L f + y' = 0 := by
      have heval :=
        congrArg (fun T : Y →L[ℝ] B => T (L f + y')) hDtEquiv
      have hzeroE : DtEquiv (L f + y') = 0 := by
        calc
          DtEquiv (L f + y') = D t (L f + y') := heval
          _ = 0 := hDsum
      apply DtEquiv.injective
      simpa only [map_zero] using hzeroE
    have hy' : y' = -L f := eq_neg_of_add_eq_zero_right hsum
    have hzm : (z : X) = m f := by
      rw [hm_apply]
      calc
        (z : X) = (f : X) + (y' : X) := hzAdd
        _ = (f : X) + ((-L f : Y) : X) := by rw [hy']
        _ = (f : X) - (L f : X) := by
          simp only [sub_eq_add_neg, Submodule.coe_neg]
    have hfRadical : f ∈ reduced.radical := by
      change reduced.toDual f = 0
      apply ContinuousLinearMap.ext
      intro g
      rw [hReducedApply]
      rw [← hzm]
      exact DFunLike.congr_fun z.property (m g)
    refine ⟨⟨f, hfRadical⟩, ?_⟩
    apply Subtype.ext
    exact hzm.symm
  let radicalEquivKernel : reduced.radical ≃ₗ[ℝ] (eta t).radical :=
    LinearEquiv.ofBijective toKernel ⟨hToKernelInjective, hToKernelSurjective⟩
  exact ⟨{
    kernelMap := m
    kernelMap_injective := hmInjective
    reducedForm := reduced
    reducedForm_apply := hReducedApply
    radicalEquivKernel := radicalEquivKernel
    radicalEquivKernel_apply := by
      intro f
      rfl
  }⟩

/-- Kernel parity is constant along a norm-continuous Fredholm path of alternating forms.

Blueprint: `thm:mod2-path`; audit: `LEM-MOD2-PATH` and `AUX-LOCAL-PARITY-GLOBAL`. -/
theorem mod2Path {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (eta : Set.Icc (0 : ℝ) 1 → ContinuousAlternatingForm X)
    (hContinuous : Continuous fun t ↦ (eta t).toDual)
    (hReflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X))
    (hFredholm : ∀ t, IsFredholm (eta t).toDual) :
    ∀ s t, Nat.ModEq 2 (Module.finrank ℝ (eta s).radical)
      (Module.finrank ℝ (eta t).radical) := by
  let k : Set.Icc (0 : ℝ) 1 → ℕ :=
    fun t => Module.finrank ℝ (eta t).radical
  have hlocal : ∀ t0, ∀ᶠ t in nhds t0, Nat.ModEq 2 (k t) (k t0) := by
    intro t0
    obtain ⟨epsilon, hepsilon, hSchur⟩ :=
      localSchurReduction (Set.Icc (0 : ℝ) 1) t0 eta hContinuous hReflexive
        (hFredholm t0)
    filter_upwards [Metric.ball_mem_nhds t0 hepsilon] with t ht
    have hclose : |(t : ℝ) - (t0 : ℝ)| < epsilon := by
      simpa [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] using ht
    obtain ⟨data⟩ := hSchur t hclose
    let : FiniteDimensional ℝ (eta t0).radical := (hFredholm t0).1
    have hparity :=
      (FiniteParity.finiteContinuousAlternatingRankEven data.reducedForm).2
    rw [data.radicalEquivKernel.finrank_eq] at hparity
    exact hparity
  have hcontinuous : Continuous (fun t => k t % 2) :=
    continuous_iff_continuousAt.2 fun t0 => by
      have heq : (fun t => k t % 2) =ᶠ[nhds t0] (fun _ => k t0 % 2) := hlocal t0
      exact continuousAt_const.congr_of_eventuallyEq heq
  intro s t
  change k s % 2 = k t % 2
  exact TotallyDisconnectedSpace.eq_of_continuous _ hcontinuous _ _

end

end KaltonPeck.Support.PathParity

/-
Upstream license notice:
MIT License

Copyright (c) 2026 Avik Das

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
