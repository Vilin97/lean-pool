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
public import LeanPool.KaltonPeck.KaltonPeck.Support.Forms
public import LeanPool.KaltonPeck.KaltonPeck.Support.Fredholm
public import LeanPool.KaltonPeck.KaltonPeck.Support.FiniteParity

/-!
# Strong symplectic forms on radical quotients

The corresponding construction from the complete finite-codimensional symplectic reduction.
-/

@[expose] public section

namespace KaltonPeck.Support.FiniteCodim

noncomputable
section

/-- A strong form on the radical quotient together with its descent identity. -/
structure FredholmQuotientStrongData {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (eta : ContinuousAlternatingForm X) where
  /-- The nondegenerate form induced on the quotient by the radical. -/
  form : StrongSymplecticForm (X ⧸ eta.radical)
  form_apply (x y : X) :
    form.toDual (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = eta.toDual x y

/-- A Fredholm alternating form descends to a strong form on its radical quotient.

Blueprint: `lem:fredholm-quotient-strong`; audit: `AUX-FREDHOLM-QUOTIENT-STRONG`. -/
def fredholmQuotientStrong {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (eta : ContinuousAlternatingForm X)
    (hReflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X))
    (hFredholm : IsFredholm eta.toDual) : FredholmQuotientStrongData eta := by
  letI : IsClosed (eta.radical : Set X) := by
    change IsClosed (eta.toDual.toLinearMap.ker : Set X)
    exact eta.toDual.isClosed_ker
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
  have hProj (x : X) : (pF x : X) + (pY x : X) = x :=
    Submodule.projectionL_add_projectionL_eq_self hTop x
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
  have hRange := Fredholm.alternatingFredholmRange eta hReflexive hFredholm
  let hSYAnn :
      SY.toLinearMap.range = Forms.continuousAnnihilator eta.radical :=
    hSY_range.trans hRange
  let SYAnnEquiv : Y ≃L[ℝ] Forms.continuousAnnihilator eta.radical :=
    eRange.trans (ContinuousLinearEquiv.ofEq SY.toLinearMap.range
      (Forms.continuousAnnihilator eta.radical) hSYAnn)
  let qY : (X ⧸ eta.radical) ≃L[ℝ] Y :=
    Submodule.quotientEquivOfIsTopCompl eta.radical Y hTop
  let qAnn : (X ⧸ eta.radical) ≃L[ℝ]
      Forms.continuousAnnihilator eta.radical :=
    qY.trans SYAnnEquiv
  let formEquiv : (X ⧸ eta.radical) ≃L[ℝ]
      StrongDual ℝ (X ⧸ eta.radical) :=
    qAnn.trans (Forms.quotientDualEquivAnnihilator eta.radical).symm
  refine
    { form :=
        { toDual := formEquiv
          alternating := ?_ }
      form_apply := ?_ }
  · intro q
    refine Submodule.Quotient.induction_on eta.radical q ?_
    intro x
    change eta.toDual (pY x : X) x = 0
    have hx : eta.toDual (pY x : X) = eta.toDual x := by
      calc
        eta.toDual (pY x : X) =
            eta.toDual ((pF x : X) + (pY x : X)) := by
              rw [map_add, hRadical, zero_add]
        _ = eta.toDual x := congrArg eta.toDual (hProj x)
    rw [hx]
    exact eta.alternating x
  · intro x y
    change eta.toDual (pY x : X) y = eta.toDual x y
    have hx : eta.toDual (pY x : X) = eta.toDual x := by
      calc
        eta.toDual (pY x : X) =
            eta.toDual ((pF x : X) + (pY x : X)) := by
              rw [map_add, hRadical, zero_add]
        _ = eta.toDual x := congrArg eta.toDual (hProj x)
    rw [hx]

end

end KaltonPeck.Support.FiniteCodim
