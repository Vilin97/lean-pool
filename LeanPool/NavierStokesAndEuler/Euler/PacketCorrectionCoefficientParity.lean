/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionSourceData
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionAssemblyParity
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderJetParity
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderParity
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketParity

/-! The source deformation symmetries imply the literal parity of the
correction coefficients, including the odd differentiated quadratic term. -/

@[expose] public section


noncomputable section

namespace EulerPacketCorrectionCoefficients

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerPacketCylinderField EulerPacketProfileRecursion
open scoped ContDiff

theorem fderiv_neg_of_even {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (hf : ContDiff ℝ ∞ f)
    (he : ∀ x, f (-x) = f x) (x : E) : fderiv ℝ f (-x) = -fderiv ℝ f x := by
  have hfun : (fun y => f (-y)) = f := funext he
  have hd := ((hf.differentiable (by simp) (-x)).hasFDerivAt).comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).neg)
  have hh : fderiv ℝ f x = -fderiv ℝ f (-x) := by
    simpa only [Function.comp_def,hfun,comp_neg,comp_id] using hd.fderiv
  simpa only [neg_neg] using (congrArg Neg.neg hh).symm

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U)
  (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
  (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)

include hF hM in
theorem frameTime_even (t : Icc (0 : ℝ) D.T) (x : Space) :
    D.F₁.field t (-x) = D.F₁.field t x := by
  apply ContinuousLinearMap.ext
  intro v
  rw [D.strain_equation,D.strain_equation,hM,hF]

variable (P : ℝ) [Fact (0 < P)]

include hF in
theorem metricTower_even (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    ((metricTower D P).coefficient t).coefficient (-x) =
      ((metricTower D P).coefficient t).coefficient x := by
  simp only [metricTower_apply,Prod.fst_neg,D.inverse_even hF]

include hF hM in
theorem linearTower_even (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    ((linearTower D P).coefficient t).coefficient (-x) =
      ((linearTower D P).coefficient t).coefficient x := by
  simp only [linearTower_apply,Prod.fst_neg,D.inverse_even hF,frameTime_even D hF hM]

include hF in
theorem quadraticTower_odd (κ : ℝ) (t : Icc (0 : ℝ) D.T) (i : Fin 3) (x : LiftDomain P) :
    ((quadraticTower D P κ i).coefficient t).coefficient (-x) =
      -((quadraticTower D P κ i).coefficient t).coefficient x := by
  rw [quadraticTower_apply,quadraticTower_apply]
  simp only [Prod.fst_neg,D.inverse_even hF,
    fderiv_neg_of_even (D.F.field t : Space → Space →L[ℝ] Space) (D.F.smooth t) (hF t),
    neg_apply,comp_neg,smul_neg]

include hF hM in
theorem correctionParityData (κ : ℝ) (hκ : |κ| ≤ 1) {z r : VectorField}
    (Z : Field P D.T z) (G : Field P D.T r)
    (hZ : JointOdd D.T z) (hG : JointOdd D.T r) :
    EulerCorrectionAssembly.ParityData P (correctionDataOfFields D P κ hκ Z G) where
  metric := metricTower_even D hF P
  linear := linearTower_even D hF hM P
  quadratic := quadraticTower_odd D hF P κ
  approximation t := by
    have h := Z.reflection_neg_of_raw_odd t (hZ t)
    change -EulerCylinderFieldReflection.reflection P (Z.path t) = Z.path t
    rw [h,neg_neg]
  residual t := by
    have h := G.reflection_neg_of_raw_odd t (hG t)
    change -EulerCylinderFieldReflection.reflection P (G.path t) = G.path t
    rw [h,neg_neg]

end EulerPacketCorrectionCoefficients
