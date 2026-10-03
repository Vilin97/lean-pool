/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
/-!
# uniqueness from the integral-closure valuation ring

Once the actual integral closure of a valuation subring satisfies the
valuative dichotomy, it is contained in every extension valuation ring.  Its
integrality over the base then forces the center of every such overring to be
the unique maximal ideal, so the overring is the integral closure itself.
-/

@[expose] public section

noncomputable
section

universe u v w

namespace DiscreteValuationField

open ValuationTheory.DiscreteValuationField.Valuation

namespace Valuation

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- the finite norm-formula theorem, uniqueness source after the actual integral closure has been
shown to be a valuation ring.

No finiteness, separability, discreteness, or completeness assumption is used:
every valuation of `L` extending the canonical valuation of `V` has valuation
subring equal to the valuation subring built from the actual integral closure
of `V` in `L`. -/
theorem normFormula_extension_valuationSubring_eq_integralClosure_of_mem_or_inv
    (V : ValuationSubring K)
    (hval :
      ∀ z : L,
        z ∈
            (integralClosure V.valuation.valuationSubring L).toSubring ∨
          z⁻¹ ∈
            (integralClosure V.valuation.valuationSubring L).toSubring)
    {Γ : Type w} [LinearOrderedCommGroupWithZero Γ]
    (wL : _root_.Valuation L Γ) [V.valuation.HasExtension wL] :
    wL.valuationSubring =
      integralClosureValuationSubringOfMemOrInv
        (L := L) V.valuation hval := by
  let B : ValuationSubring L :=
    integralClosureValuationSubringOfMemOrInv
      (L := L) V.valuation hval
  change wL.valuationSubring = B
  let : V.valuation.HasExtension B.valuation :=
    integralClosureValuationSubringOfMemOrInv_hasExtension
      (L := L) V.valuation hval
  have hBW : B ≤ wL.valuationSubring :=
    integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
      (L := L) V.valuation wL hval
  let i : V.valuation.valuationSubring →+* B :=
    { toFun := fun a =>
        ⟨algebraMap K L (a : K),
          (integralClosureValuationSubringOfMemOrInv_pullback
            (L := L) V.valuation hval (a : K)).2 a.2⟩
      map_zero' := by ext; simp
      map_one' := by ext; simp
      map_add' := by intro a b; ext; simp
      map_mul' := by intro a b; ext; simp }
  let : Algebra V.valuation.valuationSubring B := i.toAlgebra
  let : IsScalarTower V.valuation.valuationSubring B L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let P : Ideal B :=
    ValuationSubring.idealOfLE B wL.valuationSubring hBW
  have hPcomap :
      P.comap i =
        IsLocalRing.maximalIdeal V.valuation.valuationSubring := by
    apply Ideal.ext
    intro a
    rw [Ideal.mem_comap]
    change
      B.inclusion wL.valuationSubring hBW (i a) ∈
          IsLocalRing.maximalIdeal wL.valuationSubring ↔
        a ∈ IsLocalRing.maximalIdeal V.valuation.valuationSubring
    rw [Valuation.mem_maximalIdeal_iff (v := wL)]
    rw [Valuation.mem_maximalIdeal_iff (v := V.valuation)]
    have hcoe :
        ((B.inclusion wL.valuationSubring hBW (i a) :
          wL.valuationSubring) : L) = algebraMap K L (a : K) := by
      rfl
    rw [hcoe]
    exact
      _root_.Valuation.HasExtension.val_map_lt_one_iff
        V.valuation wL (a : K)
  have hBClosure :
      IsIntegralClosure B V.valuation.valuationSubring L := by
    simpa [B] using
      (integralClosureValuationSubringOfMemOrInv_isIntegralClosure
        (L := L) V.valuation hval)
  let : IsIntegralClosure B V.valuation.valuationSubring L := hBClosure
  have hBIntegral :
      Algebra.IsIntegral V.valuation.valuationSubring B :=
    IsIntegralClosure.isIntegral_algebra V.valuation.valuationSubring L
  let : Algebra.IsIntegral V.valuation.valuationSubring B := hBIntegral
  have hPmax : P.IsMaximal := by
    have hcomapMax :
        (P.comap (algebraMap V.valuation.valuationSubring B)).IsMaximal := by
      change (P.comap i).IsMaximal
      rw [hPcomap]
      exact
        IsLocalRing.maximalIdeal.isMaximal
          V.valuation.valuationSubring
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap i
      (fun x => Algebra.IsIntegral.isIntegral x) P hcomapMax
  have hP :
      ValuationSubring.idealOfLE B wL.valuationSubring hBW =
        IsLocalRing.maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal hPmax
  exact
    valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal
      B wL.valuationSubring hBW hP

end Valuation
end DiscreteValuationField

end
