/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Algebraic covariance lemmas for Zhou's dual fiber shear. Paper: §3.
-/
import LeanPool.ConnesRigidity.Paper.Section3.DualTopology

/-!
The dual action conjugacy algebra component of the Connes rigidity formalization.
-/

namespace Connes
namespace PaperDualActionConjugacyAlgebra

open Construction
open Construction.PaperKernel
open PaperDualActions
open PaperDualCoordinates
open PaperFactorIsomorphism

noncomputable section

/--
The `k` construction used in the Connes rigidity formalization.
-/
abbrev k := Construction.k
/--
The `H` construction used in the Connes rigidity formalization.
-/
abbrev H := Construction.H
/--
The `A` construction used in the Connes rigidity formalization.
-/
abbrev A := Construction.A
/--
The `PaperV` construction used in the Connes rigidity formalization.
-/
abbrev PaperV := PaperKernel.PaperV
/--
The `VStar` construction used in the Connes rigidity formalization.
-/
abbrev VStar := PaperKernel.VStar

/- Evaluation of the tensor-dual equivalence on a pure tensor. Paper: §3. -/
theorem avDualEquiv_symm_eval (z : A →ₗ[k] PaperV) (a : A) (φ : VStar) :
    avDualEquiv.symm z (a ⊗ₜ[k] φ) = φ (z a) := by
  rfl

/- Evaluation of the transpose equivalence on a pure tensor. Paper: §3. -/
theorem avDualEquiv_eval (F : Module.Dual k PaperKernel.AVStar) (a : A)
    (φ : VStar) :
    φ (avDualEquiv F a) = F (a ⊗ₜ[k] φ) := by
  change φ ((transposeFromDual (dualTensorToPartial F)) a) =
    F (a ⊗ₜ[k] φ)
  simp [transposeFromDual, dualTensorToPartial]

/- The quadratic functional used by the raw fiber shear. Paper: §3.
-/
/--
The `qTensor` construction used in the Connes rigidity formalization.
-/
def qTensor (z : A →ₗ[k] PaperV) : PaperKernel.TensorAA →ₗ[k] k :=
  PaperFactorIsomorphism.tensorFunctional
      (PaperFactorIsomorphism.coordinate z (Sum.inl 0))
      (PaperFactorIsomorphism.coordinate z (Sum.inr 0)) +
    PaperFactorIsomorphism.tensorFunctional
      (PaperFactorIsomorphism.coordinate z (Sum.inl 1))
      (PaperFactorIsomorphism.coordinate z (Sum.inr 1))

/-- The transformed first dual coordinate. Paper: §3.
-/
def zAction (h : H) (z : A →ₗ[k] PaperV) : A →ₗ[k] PaperV :=
  avDualEquiv ((avDualEquiv.symm z).comp
    (avStarAction (h⁻¹).1 (h⁻¹).2).toLinearMap)

/-- The tensor form of the second-action correction. Paper: §3.
-/
def thetaTwoTermTensor (h : H) : PaperKernel.TensorAA →ₗ[k]
    PaperKernel.AVStar :=
  ((TensorProduct.mk k A VStar).flip
      (OpenAIPort.quadraticDefectLinear (h⁻¹).2)).comp
    (PaperKernel.deltaTensor.comp
      (sl3TensorAction (h⁻¹).1))

/- Pointwise formula for the transformed first coordinate. Paper: §3. -/
theorem zAction_apply (h : H) (z : A →ₗ[k] PaperV) (a : A) :
    zAction h z a =
      qVAction h.2 (z (sl3AAction (h⁻¹).1 a)) := by
  apply (Module.evalEquiv k PaperV).injective
  ext φ
  simp only [Module.evalEquiv_apply, Module.Dual.eval_apply, zAction]
  rw [avDualEquiv_eval]
  change (avDualEquiv.symm z)
      (avStarAction (h⁻¹).1 (h⁻¹).2 (a ⊗ₜ[k] φ)) =
    φ (qVAction h.2 (z (sl3AAction (h⁻¹).1 a)))
  simp only [avStarAction, Prod.fst_inv, map_inv, qVStarActionHom,
    Prod.snd_inv, MonoidHom.coe_mk, OneHom.coe_mk,
    TensorProduct.congr_tmul, LinearEquiv.coe_inv, qVAction,
    LinearEquiv.coe_mk, LinearMap.coe_mk]
  rw [avDualEquiv_symm_eval]
  rfl

/- The inverse first action on the first dual summand. Paper: §3. -/
theorem paperThetaOne_symm_inl (h : H) (u : PaperKernel.AVStar) :
    (paperThetaOneLinear h).symm (u, 0) =
      (avStarAction (h⁻¹).1 (h⁻¹).2 u, 0) := by
  apply (paperThetaOneLinear h).injective
  rw [LinearEquiv.apply_symm_apply]
  change (u, 0) = paperThetaOneLinear h
      (avStarAction (h⁻¹).1 (h⁻¹).2 u, 0)
  change (u, 0) =
      (avStarAction h.1 h.2
          (avStarAction (h⁻¹).1 (h⁻¹).2 u),
        sl3CActionEquiv h.1 0)
  apply Prod.ext
  · have hm := avStarActionHom.map_inv h
    change avStarAction (h⁻¹).1 (h⁻¹).2 =
      (avStarAction h.1 h.2).symm at hm
    rw [hm]
    exact (avStarAction h.1 h.2).apply_symm_apply u |>.symm
  · exact (sl3CActionEquiv h.1).map_zero.symm

/- The quadratic form changes by the finite defect under the Q action.
Paper: §2. -/
theorem standardQuadraticForm_qVAction (q : PaperKernel.Q) (v : PaperV) :
    OpenAIPort.standardQuadraticForm (qVAction q v) =
      OpenAIPort.quadraticDefectLinear q⁻¹ v +
        OpenAIPort.standardQuadraticForm v := by
  change OpenAIPort.standardQuadraticForm (q • v) = _
  simp only [OpenAIPort.quadraticDefectLinear, inv_inv, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/- The inverse action on the second dual summand. Paper: §3. -/
theorem paperThetaOne_symm_inr (h : H) (c : PaperKernel.C) :
    (paperThetaOneLinearHom h).symm (0, c) =
      (0, sl3CAction (h⁻¹).1 c) := by
  apply (paperThetaOneLinear h).injective
  change paperThetaOneLinear h
      ((paperThetaOneLinear h).symm (0, c)) =
    paperThetaOneLinear h (0, sl3CAction (h⁻¹).1 c)
  rw [LinearEquiv.apply_symm_apply]
  change (0, c) =
    (avStarAction h.1 h.2 0,
      sl3CActionEquiv h.1 (sl3CAction (h⁻¹).1 c))
  apply Prod.ext
  · exact (avStarAction h.1 h.2).map_zero.symm
  · have hm := sl3CActionHom.map_inv h.1
    change sl3CActionEquiv h.1⁻¹ =
      (sl3CActionEquiv h.1).symm at hm
    change c = (sl3CActionEquiv h.1)
      (sl3CActionEquiv h.1⁻¹ c)
    rw [hm]
    exact (sl3CActionEquiv h.1).apply_symm_apply c |>.symm

/- The inverse second action on the second dual summand. Paper: §3. -/
theorem paperThetaTwo_symm_inr (h : H) (c : PaperKernel.C) :
    (paperThetaTwoLinearHom h).symm (0, c) =
      (thetaTwoTermMap (h⁻¹) c, sl3CAction (h⁻¹).1 c) := by
  apply (paperThetaTwoLinearHom h).injective
  rw [LinearEquiv.apply_symm_apply]
  change (0, c) =
    paperThetaTwoLinearEquiv h
      (thetaTwoTermMap (h⁻¹) c, sl3CAction (h⁻¹).1 c)
  change (0, c) =
    thetaTwoLinearMap h
      (thetaTwoTermMap (h⁻¹) c, sl3CAction (h⁻¹).1 c)
  change (0, c) =
    thetaTwoLinearMap h (thetaTwoLinearMap h⁻¹ (0, c))
  change (0, c) =
    ((thetaTwoLinearMap h).comp (thetaTwoLinearMap h⁻¹)) (0, c)
  rw [← thetaTwoLinearMap_mul]
  rw [show h * h⁻¹ = (1 : H) by simp]
  rw [thetaTwoLinearMap_one]
  rfl

/- The raw and homomorphism forms of the first action agree. Paper: §3. -/
theorem paperThetaOneHom_symm_eq (h : H) :
    (paperThetaOneLinearHom h).symm = (paperThetaOneLinear h).symm := by
  apply LinearEquiv.ext
  intro d
  rfl

end
end PaperDualActionConjugacyAlgebra
end Connes
