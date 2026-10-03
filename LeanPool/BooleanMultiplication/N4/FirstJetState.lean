/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.FirstJetSupport

/-!
# The post-first-feedback circuit state

The geometric first-jet theorem is connected here to the actual circuit flag.
The target witness entering at gate five is replaced, modulo the preceding
state, by its rational tangent.  Thus later gates see the old seed state plus
one explicit first-Hasse-jet direction.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- The normalized seed and fifth-gate target data at a rational first jet. -/
@[expose]
def FirstJetState (C : Circuit 8 8) : Prop :=
  ∃ (theta : Fin 3) (eps : F₂)
    (seedLinear seedCompanion : LinearForm) (seedRho : F₂),
    anfThreeProjection (C.gate 3) =
      vectorWedgeTwo seedLinear (rationalTwo (rationalSingleton theta)) ∧
    anfTwoProjection (C.gate 3) =
      seedRho • rationalTwo (rationalSingleton theta) +
        vectorWedge seedCompanion seedLinear +
        booleanContraction seedLinear
          (rationalTwo (rationalSingleton theta)) ∧
    vectorWedgeTwo seedLinear (rationalTwo (rationalSingleton theta)) ≠ 0 ∧
    InNormalizedFirstJet theta seedLinear ∧
    circuitFlag C 5 = circuitFlag C 4 ⊔
      Submodule.span F₂ {targetANF (rationalTangentAt theta eps)}

/-- The first useful suffix gate installs the first Hasse jet in the actual
circuit flag.  All coordinate work is delegated to the correlated algebraic
normal form; this proof only performs state replacement. -/
theorem NormalizedEight.firstJetState
    {C : Circuit 8 8} (h : NormalizedEight C) : FirstJetState C := by
  rcases h.firstUsefulChild_isLowLow with
    ⟨target, child, shift, htarget, htargetOld, htargetNew, hshift,
      htargetEq, hchild⟩
  rcases h.cubicLowLowCollision_of_firstUsefulChild
      htarget htargetOld hshift htargetEq hchild with
    ⟨low, hlow, htargetNotLow, hcollision⟩
  rcases h.cubicLowLowNormalCollisionAt hchild hlow htarget htargetNotLow hcollision with
    ⟨targetAffine, targetCoeff, hAt⟩
  rcases cubicLowLowNormalCollisionAt_targetNormalForm hAt with
    ⟨theta, eps, seedLinear, seedCompanion, seedRho, rationalCoeff,
      htargetAffine, htargetRep, hgCubic, hgQuadratic, hgCubicNonzero,
      hdelta, hnormal⟩
  let jet : ANF 8 := targetANF (rationalTangentAt theta eps)
  let oldPart : ANF 8 := targetAffine + rationalANF rationalCoeff
  have holdPartLow : oldPart ∈ rationalLowSpace := by
    dsimp [oldPart]
    apply Submodule.add_mem
    · exact Submodule.mem_sup_left htargetAffine
    · exact Submodule.mem_sup_right
        ((mem_rationalTargetSpace_iff _).mpr ⟨rationalCoeff, rfl⟩)
  have holdPart : oldPart ∈ circuitFlag C 4 := by
    rw [h.wireSpace_four_eq]
    exact Submodule.mem_sup_left holdPartLow
  have hjetEq : jet = target + oldPart := by
    dsimp [jet, oldPart]
    rw [← hdelta]
    change targetANFLinear (targetCoeff + rationalCoeffRep rationalCoeff) = _
    rw [map_add, htargetRep]
    change targetANF targetCoeff + rationalANF rationalCoeff =
      (targetAffine + targetANF targetCoeff) +
        (targetAffine + rationalANF rationalCoeff)
    rw [add_add_add_comm, anf_add_self, zero_add]
  have hjetOld : jet ∉ circuitFlag C 4 := by
    intro hj
    apply htargetOld
    have hsum := Submodule.add_mem _ hj holdPart
    have heq : jet + oldPart = target := by
      rw [hjetEq]
      rw [add_assoc, anf_add_self, add_zero]
    rwa [heq] at hsum
  have hjetNew : jet ∈ circuitFlag C 5 := by
    rw [hjetEq]
    exact Submodule.add_mem _ htargetNew
      (wireSpace_mono (g := C.gate) (by omega) holdPart)
  refine ⟨theta, eps, seedLinear, seedCompanion, seedRho,
    hgCubic, hgQuadratic, hgCubicNonzero, hnormal, ?_⟩
  exact circuit_first_entry_replacement C (4 : Fin 8) jet hjetNew hjetOld

end

end N4
end UnrestrictedBooleanMul
