/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Action-indexed finite-extension data for the Zhou semidirect products.
Paper: §4.
-/
import LeanPool.ConnesRigidity.Paper.Section4.SplitExtensions

/-!
The finite extensions component of the Connes rigidity formalization.
-/

namespace Connes
namespace PaperFiniteExtensions

open Construction
open Construction.PaperKernel
open PaperPropertyT

noncomputable section

/--
The `N` construction used in the Connes rigidity formalization.
-/
abbrev N := Multiplicative PaperKernel.D
/--
The `S` construction used in the Connes rigidity formalization.
-/
abbrev S := SpecialLinear.SL3
/--
The `Q` construction used in the Connes rigidity formalization.
-/
abbrev Q := PaperKernel.Q

/-- The finite quotient map records the Sp₄(F₂) coordinate. Paper: §4. -/
def quotientQ (action : H →* MulAut N) :
    PaperKernel.paperGammaCarrier action →* Q :=
  (MonoidHom.snd S Q).comp
    (SemidirectProduct.rightHom (N := N) (G := H) (φ := action))

theorem quotientQ_surjective (action : H →* MulAut N) :
    Function.Surjective (quotientQ action) := by
  intro q
  refine ⟨SemidirectProduct.inr (1, q), ?_⟩
  rfl

/-- The intermediate semidirect product embeds as the kernel of the finite quotient. Paper: §4. -/
def liftLambda (action : H →* MulAut N) :
    lambdaCarrier action →* PaperKernel.paperGammaCarrier action :=
  SemidirectProduct.map (MonoidHom.id N) sl3ToActingGroup (by
    intro s
    rfl)

/-- The intermediate group is identified with the finite-index kernel. Paper: §4. -/
def lambdaToSubgroup (action : H →* MulAut N) :
    lambdaCarrier action ≃* (quotientQ action).ker where
  toFun x := ⟨liftLambda action x, by
    apply MonoidHom.mem_ker.mpr
    rfl⟩
  invFun x := ⟨x.1.left, x.1.right.1⟩
  left_inv x := by
    apply SemidirectProduct.ext <;> rfl
  right_inv x := by
    apply Subtype.ext
    change
      (⟨x.1.left, (x.1.right.1, 1)⟩ :
        PaperKernel.paperGammaCarrier action) = x.1
    apply SemidirectProduct.ext
    · rfl
    · apply Prod.ext
      · rfl
      · have hx := MonoidHom.mem_ker.mp x.property
        change x.1.right.2 = 1 at hx
        exact hx.symm
  map_mul' x y := by
    apply Subtype.ext
    exact (liftLambda action).map_mul x y

private theorem quotient_finite (action : H →* MulAut N) :
    Finite ((PaperKernel.paperGammaCarrier action) ⧸
      (quotientQ action).ker) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective
    (quotientQ action) (quotientQ_surjective action)
  exact Finite.of_injective (fun x => e x) e.injective

/-- The finite extension associated to a kernel action. Paper: §4. -/
def finiteExtension
    (action : H →* MulAut N) :
    PropertyTTransfer.FiniteExtensionData
      (lambdaOf action) (PaperKernel.paperGammaOf action)
      finiteSymplecticGroup := by
  let Nq := (quotientQ action).ker
  let hN : Nq.Normal := (quotientQ action).normal_ker
  let _ : Finite ((PaperKernel.paperGammaOf action : Type) ⧸ Nq) := by
    exact quotient_finite action
  have hindex : Nq.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  have hquotient :
      CountableDiscreteGroup.quotient
          (PaperKernel.paperGammaOf action) Nq hN ≃*
        finiteSymplecticGroup := by
    exact QuotientGroup.quotientKerEquivOfSurjective
      (quotientQ action) (quotientQ_surjective action)
  exact {
    subgroup := Nq
    normal := hN
    finiteIndex := hindex
    subgroupEquiv := lambdaToSubgroup action
    quotientEquiv := hquotient }

end
end PaperFiniteExtensions
end Connes
