/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-
-/
import LeanPool.ConnesRigidity.Paper.Section3.DualTopology

/-!
# Dual automorphisms of Zhou's compact kernel

This file packages the dual of a discrete automorphism of the concrete kernel
and proves continuity and Haar preservation. It is the common §3 input for
the crossed-action conjugacy and the §4 spectral detector.
-/

namespace Connes
namespace PaperDualAutomorphism

open MeasureTheory
open Construction
open Construction.PaperKernel
open PaperDualHaar
open PaperDualTopology

noncomputable section

/--
The `D` construction used in the Connes rigidity formalization.
-/
abbrev D := PaperKernel.D
/--
The `CharacterSpace` construction used in the Connes rigidity formalization.
-/
abbrev CharacterSpace := PaperDualTopology.CharacterSpace

/--
The `continuousMulAut` construction used in the Connes rigidity formalization.
-/
def continuousMulAut (e : AddAut D) :
    Multiplicative D →ₜ* Multiplicative D where
  toFun x := Multiplicative.ofAdd (e x.toAdd)
  map_one' := by simp
  map_mul' x y := by simp [map_add]
  continuous_toFun := continuous_of_discreteTopology

@[simp] theorem continuousMulAut_apply (e : AddAut D) (x : Multiplicative D) :
    continuousMulAut e x = Multiplicative.ofAdd (e x.toAdd) := rfl

/-- The dual automorphism is precomposition by the inverse kernel automorphism. -/
def dualCharacterEquiv (e : AddAut D) : CharacterSpace ≃+ CharacterSpace where
  toFun χ := Additive.ofMul
    (PontryaginDual.map (continuousMulAut e.symm) (Additive.toMul χ))
  invFun χ := Additive.ofMul
    (PontryaginDual.map (continuousMulAut e) (Additive.toMul χ))
  left_inv χ := by
    apply Additive.toMul.injective
    apply PontryaginDual.ext
    intro x
    change (PontryaginDual.map (continuousMulAut e)
      (PontryaginDual.map (continuousMulAut e.symm)
        (Additive.toMul χ))) x = (Additive.toMul χ) x
    rw [PontryaginDual.map_apply, PontryaginDual.map_apply]
    rw [continuousMulAut_apply, continuousMulAut_apply]
    simp
  right_inv χ := by
    apply Additive.toMul.injective
    apply PontryaginDual.ext
    intro x
    change (PontryaginDual.map (continuousMulAut e.symm)
      (PontryaginDual.map (continuousMulAut e)
        (Additive.toMul χ))) x = (Additive.toMul χ) x
    rw [PontryaginDual.map_apply, PontryaginDual.map_apply]
    rw [continuousMulAut_apply, continuousMulAut_apply]
    simp
  map_add' χ ψ := by
    apply Additive.toMul.injective
    apply PontryaginDual.ext
    intro x
    change (χ + ψ) (e.symm x.toAdd) =
      χ (e.symm x.toAdd) * ψ (e.symm x.toAdd)
    rfl

@[simp] theorem dualCharacterEquiv_apply (e : AddAut D) (χ : CharacterSpace)
    (x : D) :
    (Additive.toMul (dualCharacterEquiv e χ)) (Multiplicative.ofAdd x) =
      (Additive.toMul χ) (Multiplicative.ofAdd (e.symm x)) := by
  rfl

theorem dualCharacterEquiv_continuous (e : AddAut D) :
    Continuous (dualCharacterEquiv e) := by
  change Continuous (PontryaginDual.map (continuousMulAut e.symm))
  exact (PontryaginDual.map (continuousMulAut e.symm)).continuous_toFun

end
end PaperDualAutomorphism
end Connes
