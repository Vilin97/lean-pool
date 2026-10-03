/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.Cubic
public import LeanPool.BooleanMultiplication.N4.QuadraticLower

/-!
# Rational-prefix rigidity

This file proves the algebraic core of the manuscript's prefix proposition.
If two wires have quadratic parts in the three rational-place space and their
product has no cubic or quartic part, then any target quadratic shadow of that
product is again in the rational-place space.  No circuit enumeration is used.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

theorem targetTwo_rationalPlaceCoeff (θ : Fin 3) :
    targetTwo (rationalPlaceCoeff θ) = rationalPlaceTwo θ := by
  funext i j
  fin_cases θ <;> fin_cases i <;> fin_cases j <;>
    simp [targetTwo, rationalPlaceCoeff, rationalPlaceTwo, vectorWedge, placeA, placeB,
      rZeroCoeff, rOneCoeff, rInfinityCoeff]

theorem rationalPlaceTwo_ne_zero (θ : Fin 3) : rationalPlaceTwo θ ≠ 0 := by
  intro h
  fin_cases θ
  · have hc := congrFun (congrFun h 0) 4
    simp [rationalPlaceTwo, vectorWedge, placeA, placeB] at hc
  · have hc := congrFun (congrFun h 0) 4
    simp [rationalPlaceTwo, vectorWedge, placeA, placeB] at hc
  · have hc := congrFun (congrFun h 3) 7
    simp [rationalPlaceTwo, vectorWedge, placeA, placeB] at hc

theorem rationalPlaceTwo_mem (θ : Fin 3) :
    rationalPlaceTwo θ ∈ rationalPlaceTwoSpace := by
  rw [← targetTwo_rationalPlaceCoeff]
  exact Submodule.subset_span ⟨θ, rfl⟩

theorem rationalTwo_mem (γ : Fin 3 → F₂) :
    rationalTwo γ ∈ rationalPlaceTwoSpace := by
  rw [rationalTwo]
  exact Submodule.sum_mem _ fun θ _ =>
    Submodule.smul_mem _ _ (rationalPlaceTwo_mem θ)

theorem rationalPlaceTwoSpace_le_targetTwoSpace :
    rationalPlaceTwoSpace ≤ targetTwoSpace := by
  rw [rationalPlaceTwoSpace, Submodule.span_le]
  rintro q ⟨θ, rfl⟩
  exact ⟨rationalPlaceCoeff θ, rfl⟩

/-- A vanishing rational cubic contraction has only a rational quadratic
degree-lowering shadow. -/
theorem rational_contraction_mem_of_cubic_zero
    (γ : Fin 3 → F₂) (N : LinearForm)
    (h : vectorWedgeTwo N (rationalTwo γ) = 0) :
    booleanContraction N (rationalTwo γ) ∈ rationalPlaceTwoSpace := by
  by_cases hγ : γ = 0
  · subst γ
    rw [rationalTwo_zero]
    have hz : booleanContraction N (0 : TwoForm) = 0 := by
      funext i j
      simp [booleanContraction]
    rw [hz]
    exact Submodule.zero_mem _
  by_cases hN : N = 0
  · subst N
    have hz : booleanContraction (0 : LinearForm) (rationalTwo γ) = 0 := by
      funext i j
      simp [booleanContraction]
    rw [hz]
    exact Submodule.zero_mem _
  have hdecomp : IsDecomposableTwo (rationalTwo γ) := by
    have hN3 : vectorWedgeTwoN N (rationalTwo γ) = 0 := by
      funext i j k
      have hc := congrFun (congrFun (congrFun h i) j) k
      simpa [vectorWedgeTwoN, vectorWedgeTwo] using hc
    rcases decomposable_of_vectorWedgeTwoN_zero N (rationalTwo γ) hN
        hN3 with ⟨v, hv⟩
    refine ⟨N, v, ?_⟩
    funext i j
    have hc := congrFun (congrFun hv i) j
    simpa [vectorWedgeN, vectorWedge] using hc
  have hcoeff : rationalCoeffRep γ ≠ 0 := by
    intro hz
    apply hγ
    apply rationalCoeffRep_injective
    simpa [rationalCoeffRep] using hz
  have htargetDec : IsDecomposableTwo (targetTwo (rationalCoeffRep γ)) := by
    rw [targetTwo_rationalCoeffRep]
    exact hdecomp
  have hcase (θ : Fin 3)
      (hcoeffθ : rationalCoeffRep γ = rationalPlaceCoeff θ) :
      booleanContraction N (rationalTwo γ) ∈ rationalPlaceTwoSpace := by
    have hq : rationalTwo γ = rationalPlaceTwo θ := by
      calc
        rationalTwo γ = targetTwo (rationalCoeffRep γ) :=
          (targetTwo_rationalCoeffRep γ).symm
        _ = targetTwo (rationalPlaceCoeff θ) := by rw [hcoeffθ]
        _ = rationalPlaceTwo θ := targetTwo_rationalPlaceCoeff θ
    have hsupp : vectorWedgeTwo N
        (vectorWedge (placeA θ) (placeB θ)) = 0 := by
      simpa [rationalPlaceTwo, hq] using h
    rcases mem_support_of_vectorWedgeTwo_zero N (placeA θ) (placeB θ)
        (by simpa [rationalPlaceTwo] using rationalPlaceTwo_ne_zero θ)
        hsupp with ⟨a, b, hNab⟩
    rw [hq, hNab, booleanContraction_rationalPlace]
    exact Submodule.smul_mem _ _ (rationalPlaceTwo_mem θ)
  rcases decomposableTarget_classification
      (targetTwo_decomposableTarget htargetDec) hcoeff with hzero | hone | hinf
  · exact hcase 0 (by simpa [rationalPlaceCoeff] using hzero)
  · exact hcase 1 (by simpa [rationalPlaceCoeff] using hone)
  · exact hcase 2 (by simpa [rationalPlaceCoeff] using hinf)

/-- Recover rational Hankel coefficients from membership of the exterior
two-form in the rational-place span. -/
theorem coeff_mem_rational_of_targetTwo_mem {c : TargetCoeff}
    (hc : targetTwo c ∈ rationalPlaceTwoSpace) :
    c ∈ rationalCoeffSpace := by
  rw [rationalPlaceTwoSpace] at hc
  rcases (Submodule.mem_span_range_iff_exists_fun
      (R := F₂)
      (v := fun θ : Fin 3 => targetTwo (rationalPlaceCoeff θ))
      (x := targetTwo c)).mp hc with ⟨γ, hγ⟩
  have hforms : rationalTwo γ = targetTwo c := by
    rw [rationalTwo]
    simpa only [targetTwo_rationalPlaceCoeff] using hγ
  have hcoeff : rationalCoeffRep γ = c := by
    apply targetTwo_injective
    rw [targetTwo_rationalCoeffRep]
    exact hforms
  rw [← hcoeff]
  exact rationalCoeffRep_mem γ

/-- Exterior prefix rigidity.  The hypotheses are precisely the quartic,
cubic, and quadratic homogeneous equations for a low product landing in the
target space. -/
theorem exterior_prefix_rigidity
    (a b : F₂) (ell m : LinearForm) (α β : Fin 3 → F₂)
    (c : TargetCoeff)
    (hquartic : wedgeTwo (rationalTwo α) (rationalTwo β) = 0)
    (hcubic : rationalProductCubic ell m α β = 0)
    (hquadratic :
      targetTwo c = rationalProductQuadratic a b ell m α β) :
    c ∈ rationalCoeffSpace := by
  rcases low_product_quadratic_normal_form_weak a b ell m α β hquartic with
    ⟨γ, N, z, ρ, hcube, hquad⟩
  have hN : vectorWedgeTwo N (rationalTwo γ) = 0 := by
    rw [← hcube, hcubic]
  have hG := rationalTwo_mem γ
  have hk := rational_contraction_mem_of_cubic_zero γ N hN
  have htarget : targetTwo c ∈ targetTwoSpace := ⟨c, rfl⟩
  have hGtarget := rationalPlaceTwoSpace_le_targetTwoSpace hG
  have hktarget := rationalPlaceTwoSpace_le_targetTwoSpace hk
  have hwEq : vectorWedge z N =
      targetTwo c + ρ • rationalTwo γ +
        booleanContraction N (rationalTwo γ) := by
    rw [hquadratic, hquad]
    funext i j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]
  have hwTarget : vectorWedge z N ∈ targetTwoSpace := by
    rw [hwEq]
    exact Submodule.add_mem _
      (Submodule.add_mem _ htarget (Submodule.smul_mem _ _ hGtarget)) hktarget
  have hwRat : vectorWedge z N ∈ rationalPlaceTwoSpace := by
    apply decomposable_mem_rationalPlaceTwoSpace hwTarget
    exact ⟨z, N, rfl⟩
  have hcTwo : targetTwo c ∈ rationalPlaceTwoSpace := by
    rw [hquadratic, hquad]
    exact Submodule.add_mem _
      (Submodule.add_mem _ (Submodule.smul_mem _ _ hG) hwRat) hk
  exact coeff_mem_rational_of_targetTwo_mem hcTwo

end

end N4
end UnrestrictedBooleanMul
