/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Action-indexed split-extension presentations for Zhou §4. These expose the
semidirect-product inclusion, quotient, section, and conjugation used by the
spectral criterion; they do not prove the paper-specific spectral input.
-/
import LeanPool.ConnesRigidity.Paper.Section4.PropertyT
import LeanPool.ConnesRigidity.Foundation.GroupTheory.SplitAbelianExtension

/-!
The split extensions component of the Connes rigidity formalization.
-/

namespace Connes
namespace PaperSplitExtensions

open Construction
open Construction.PaperKernel
open PaperPropertyT

noncomputable section

private theorem semidirectConjugation
    {N G : Type*} [Group N] [Group G]
    (φ : G →* MulAut N) (g : G) (n : N) :
    SemidirectProduct.inr g * SemidirectProduct.inl n *
        (SemidirectProduct.inr g)⁻¹ =
      (SemidirectProduct.inl (φ g n) : SemidirectProduct N G φ) :=
  by simpa only [map_inv] using (SemidirectProduct.inl_aut g n).symm

/-- The SL₃ semidirect product as a split abelian extension. Paper: §4. -/
noncomputable def lambdaExtension
    (action : H →* MulAut (Multiplicative PaperKernel.D)) :
    SplitAbelianExtension PaperKernel.D
      (PaperPropertyT.lambdaOf action) SpecialLinear.sl3Group := {
  inclusion := SemidirectProduct.inl
  quotient := SemidirectProduct.rightHom
  splitting := SemidirectProduct.inr
  quotient_splitting := SemidirectProduct.rightHom_comp_inr
  exact := SemidirectProduct.range_inl_eq_ker_rightHom.symm
  action := (MulAutMultiplicative PaperKernel.D).toMonoidHom.comp
    (action.comp sl3ToActingGroup)
  conjugation h a := by
    change
      (⟨1, (h : SpecialLinear.SL3)⟩ :
          SemidirectProduct (Multiplicative PaperKernel.D)
            SpecialLinear.SL3
            (action.comp sl3ToActingGroup)) *
        (⟨Multiplicative.ofAdd a, 1⟩ :
          SemidirectProduct (Multiplicative PaperKernel.D)
            SpecialLinear.SL3
            (action.comp sl3ToActingGroup)) *
        (⟨1, (h : SpecialLinear.SL3)⟩ :
            SemidirectProduct (Multiplicative PaperKernel.D)
            SpecialLinear.SL3
            (action.comp sl3ToActingGroup))⁻¹ =
      (⟨(action.comp sl3ToActingGroup) h
          (Multiplicative.ofAdd a), 1⟩ :
        SemidirectProduct (Multiplicative PaperKernel.D)
          SpecialLinear.SL3
          (action.comp sl3ToActingGroup))
    exact semidirectConjugation _ _ _ }

/-- The kernel inclusion of the action-indexed extension is the semidirect
product inclusion. Paper: §4. -/
theorem lambdaExtension_inclusion
    (action : H →* MulAut (Multiplicative PaperKernel.D))
    (a : Multiplicative PaperKernel.D) :
    (lambdaExtension action).inclusion a =
      (SemidirectProduct.inl a : (lambdaOf action : Type)) := rfl

/-- The quotient of the action-indexed extension is the semidirect-product
projection. Paper: §4. -/
theorem lambdaExtension_quotient
    (action : H →* MulAut (Multiplicative PaperKernel.D))
    (x : (lambdaOf action : Type)) :
    (lambdaExtension action).quotient x = x.right := rfl

/-- The splitting of the action-indexed extension is the semidirect-product
section. Paper: §4. -/
theorem lambdaExtension_splitting
    (action : H →* MulAut (Multiplicative PaperKernel.D))
    (g : SpecialLinear.SL3) :
    (lambdaExtension action).splitting g =
      (SemidirectProduct.inr g : (lambdaOf action : Type)) := rfl

/-- The extension action is the restriction of the given action along the
standard inclusion `SL₃ → SL₃ × Sp₄(𝔽₂)`. Paper: §4. -/
@[simp] theorem lambdaExtension_action
    (action : H →* MulAut (Multiplicative PaperKernel.D))
    (g : SpecialLinear.SL3) :
    (lambdaExtension action).action g =
      ((MulAutMultiplicative PaperKernel.D).toMonoidHom.comp action)
        (sl3ToActingGroup g) := rfl

end

end PaperSplitExtensions
end Connes
