/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCorrectorOperator
import LeanPool.NavierStokesAndEuler.Euler.PacketPotentialRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketAngularPotential
import LeanPool.NavierStokesAndEuler.Euler.AnglePrimitiveParity

/-! The literal corrector preserves joint odd parity under the actual even inverse deformation. -/

section

/-! Jointly odd transverse profiles give the actual jointly even vector potential. -/

@[expose] public section

noncomputable section

namespace EulerPacketAngularPotential

open EulerSmoothLimit EulerPacketCrossProduct EulerAngleMeanZeroPrimitive MeasureTheory

theorem potential_joint_even (P : ℝ) (hP : P ≠ 0) (m : Space → Space)
    (A : Space → ℝ → Space) (hm : ∀ x, m (-x) = m x)
    (hA : ∀ x, Continuous (A x)) (hper : ∀ x, Function.Periodic (A x) P)
    (hmean : ∀ x, ∫ θ in 0..P, A x θ = 0)
    (hodd : ∀ x θ, A (-x) (-θ) = -A x θ) (x : Space) (θ : ℝ) :
    potential P (m (-x)) (A (-x)) (-θ)=potential P (m x) (A x) θ := by
  let f : ℝ → Space := fun s => potentialMultiplier (m x) (A x s)
  have hf : Continuous f := (potentialMultiplier (m x)).continuous.comp (hA x)
  have hp : Function.Periodic f P := fun s => congrArg (potentialMultiplier (m x)) (hper x s)
  have hz : (∫ s in 0..P, f s)=0 := by
    change (∫ s in 0..P, potentialMultiplier (m x) (A x s))=0
    rw [(potentialMultiplier (m x)).intervalIntegral_comp_comm ((hA x).intervalIntegrable 0 P),
      hmean x, map_zero]
  have he : (fun s => potentialMultiplier (m (-x)) (A (-x) s))=fun s => -f (-s) := by
    funext s
    rw [hm]
    have ha : A (-x) s=-A x (-s) := by simpa only [neg_neg] using hodd x (-s)
    rw [ha, map_neg]
  change primitive P (fun s => potentialMultiplier (m (-x)) (A (-x) s)) (-θ)=primitive P f θ
  rw [he, primitive_reflection P hP f hf hp hz]
  simp only [neg_neg]

end EulerPacketAngularPotential

end
end

end

@[expose] public section

noncomputable section

namespace EulerTransversePacketProvider

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerPacketProfileRecursion
  EulerPacketPiola EulerPacketAngularPotential EulerCylinderSmoothOrbit
open scoped ContDiff

private theorem fderiv_of_even (f : LiftTangent → Space) (hf : ContDiff ℝ ∞ f)
    (he : ∀ z, f (-z) = f z) (z : LiftTangent) : fderiv ℝ f (-z) = -fderiv ℝ f z := by
  have hd := ((hf.differentiable (by simp) (-z)).hasFDerivAt).comp z
    ((hasFDerivAt_id (𝕜 := ℝ) z).neg)
  have heq : (fun y => f (-y)) = f := funext he
  have h : fderiv ℝ f z = -fderiv ℝ f (-z) := by
    simpa only [Function.comp_def, heq, comp_neg, comp_id] using hd.fderiv
  simpa only [neg_neg] using congrArg Neg.neg h.symm

namespace Data

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] (D : Data U)
  (P : ℝ) [Fact (0 < P)] (A : VectorField) (t : ℝ)

theorem rawPotential_smooth (hA : ContDiff ℝ ∞ (fun y : LiftTangent => A (t,y))) :
    ContDiff ℝ ∞ (fun y : LiftTangent => D.rawPotential P A (t,y)) := by
  have hn (x : Space) : D.normal.field (D.clamp t) x ≠ 0 := by
    intro hz
    have hl := D.normal_lower (D.clamp t) x
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hl
    exact (not_le_of_gt D.normalLower_pos) hl
  exact coveringPotential_contDiff P (Fact.out : 0 < P).le
    (fun x => D.normal.field (D.clamp t) x) (fun y => A (t,y))
    (D.normal.smooth (D.clamp t)) hn hA

variable (hInv : ∀ x, D.FInv.field (D.clamp t) (-x) = D.FInv.field (D.clamp t) x)
  (hA : ContDiff ℝ ∞ (fun y : LiftTangent => A (t, y)))
  (hper : ∀ x, Function.Periodic (fun θ => A (t, (x, θ))) P)
  (hmean : ∀ x, (∫ θ in (0 : ℝ)..P, A (t, (x, θ))) = 0)
  (hodd : ∀ x θ, A (t, (-x, -θ)) = -A (t, (x, θ)))

include hInv hA hper hmean hodd in
theorem rawPotential_even (x : Space) (θ : ℝ) :
    D.rawPotential P A (t,(-x,-θ)) = D.rawPotential P A (t,(x,θ)) := by
  have hn (y : Space) : D.normal.field (D.clamp t) (-y) = D.normal.field (D.clamp t) y := by
    change (D.FInv.field (D.clamp t) (-y)).adjoint D.m₀ = (D.FInv.field (D.clamp t) y).adjoint D.m₀
    rw [hInv]
  exact potential_joint_even P (Fact.out : 0 < P).ne'
    (fun y => D.normal.field (D.clamp t) y) (fun y θ => A (t,(y,θ))) hn
    (fun y => hA.continuous.comp (continuous_const.prodMk continuous_id)) hper hmean hodd x θ

include hInv hA hper hmean hodd in
theorem curlCorrector_odd (x : Space) (θ : ℝ) :
    D.curlCorrector P A (t,(-x,-θ)) = -D.curlCorrector P A (t,(x,θ)) := by
  have he (z : LiftTangent) : D.rawPotential P A (t,-z) = D.rawPotential P A (t,z) :=
    D.rawPotential_even P A t hInv hA hper hmean hodd z.1 z.2
  have hd := fderiv_of_even (fun z : LiftTangent => D.rawPotential P A (t,z))
    (D.rawPotential_smooth P A t hA) he (x,θ)
  change curlOperator
      ((fderiv ℝ (fun z : LiftTangent => D.rawPotential P A (t,z)) (-(x,θ))).comp
        ((ContinuousLinearMap.inl ℝ Space ℝ).comp (D.FInv.field (D.clamp t) (-x)))) =
    -curlOperator
      ((fderiv ℝ (fun z : LiftTangent => D.rawPotential P A (t,z)) (x,θ)).comp
        ((ContinuousLinearMap.inl ℝ Space ℝ).comp (D.FInv.field (D.clamp t) x)))
  rw [hd, hInv, neg_comp, map_neg]

end Data

namespace Forcing

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)

theorem corrector_odd (t : Icc (0 : ℝ) D.T)
    (hInv : ∀ x, D.FInv.field t (-x) = D.FInv.field t x)
    (hA : ∀ x θ, G.vector I (t, (-x, -θ)) = -G.vector I (t, (x, θ))) (x : Space) (θ : ℝ) :
    G.corrector I (t,(-x,-θ)) = -G.corrector I (t,(x,θ)) := by
  rw [← G.curlCorrector_eq I t (-x) (-θ), ← G.curlCorrector_eq I t x θ]
  apply D.curlCorrector_odd P (G.vector I) t
  · simpa only [D.clamp_coe] using hInv
  · exact G.vector_spatial_smooth I t
  · exact G.vector_periodic I t
  · exact G.vector_mean_zero I t
  · exact hA

end Forcing
end EulerTransversePacketProvider
