/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryScaling
public import LeanPool.NavierStokesAndEuler.Euler.PacketPressureFastHessian

@[expose] public section

/-! The primary's literal velocity gradient at every spatial point.  Its
fast derivative is the source shear, and the slow derivative has an
explicit inverse-frequency factor. -/

noncomputable section

namespace EulerPacketPrimaryShear

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerTransversePacketPrimary EulerPacketTerminalDatum
  EulerPacketPrimaryFactorization EulerPacketGraphHessian EulerGraphPullback
  EulerPacketCylinderField EulerLiftedGradientSpace EulerPeriodicProfile
  EulerCylinderCoordinates EulerCylinderSobolevSpace EulerGevrey
open scoped ContDiff

def slowGraphDerivative (q : LiftTangent → Space) (k : ℝ) (m : Space)
    (Y : Space → Space) (J : Space →L[ℝ] Space) (x : Space) : Space →L[ℝ] Space :=
  k⁻¹ • ((fderiv ℝ q (graphMap k m (Y x))).comp (inl ℝ Space ℝ)).comp J

theorem graph_vector_hasFDerivAt (q : LiftTangent → Space) (k : ℝ) (hk : k ≠ 0)
    (m : Space) (Y : Space → Space) (J : Space →L[ℝ] Space) (x : Space)
    (hY : HasFDerivAt Y J x) (hq : DifferentiableAt ℝ q (graphMap k m (Y x))) :
    HasFDerivAt (fun y => k⁻¹ • q (graphMap k m (Y y)))
      (rankOne ℝ (fderiv ℝ q (graphMap k m (Y x)) (0,1)) (J.adjoint m)+
        slowGraphDerivative q k m Y J x) x := by
  have hg : HasFDerivAt (fun y => graphMap k m (Y y)) ((graphMap k m).comp J) x :=
    (graphMap k m).hasFDerivAt.comp x hY
  convert! (hq.hasFDerivAt.comp x hg).const_smul k⁻¹ using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [slowGraphDerivative,add_apply,smul_apply,comp_apply,rankOne_apply,
    graph_decomposition,map_add,map_smul,inl_apply,smul_add,smul_smul]
  rw [← J.adjoint_inner_left v m]
  match_scalars <;> field_simp

theorem slowGraphDerivative_norm_le (q : LiftTangent → Space) (k : ℝ) (m : Space)
    (Y : Space → Space) (J : Space →L[ℝ] Space) (x : Space) :
    ‖slowGraphDerivative q k m Y J x‖ ≤
      |k⁻¹| * ‖fderiv ℝ q (graphMap k m (Y x))‖ * ‖J‖ := by
  unfold slowGraphDerivative
  rw [norm_smul,Real.norm_eq_abs,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply (opNorm_comp_le _ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [norm_inl,mul_one] using
    opNorm_comp_le (fderiv ℝ q (graphMap k m (Y x))) (inl ℝ Space ℝ)

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support)

theorem scaled_terminal_angular_fderiv (a : ℝ) (t : Icc (0 : ℝ) D.T) (z : LiftTangent) :
    fderiv ℝ (fun y => vector τ hτ hτT B (initialData D δ hδ (a • ξ) hs) (t,y)) z (0,1) =
      (a*deriv (profile δ) z.2) • canonicalVelocity τ hτ hτT B ξ hs t z.1 := by
  let q : LiftTangent → Space := fun y =>
    vector τ hτ hτT B (initialData D δ hδ (a • ξ) hs) (t,y)
  have he : (fun θ => q (z.1,θ)) = fun θ =>
      a • (profile δ θ • canonicalVelocity τ hτ hτT B ξ hs t z.1) := by
    funext θ
    dsimp only [q]
    rw [vector_terminal_smul,vector_factorization_canonical]
  have hd := (((profile_hasDerivAt δ hδ z.2).differentiableAt.hasDerivAt).smul_const
    (canonicalVelocity τ hτ hτT B ξ hs t z.1)).const_smul a
  have hq : DifferentiableAt ℝ q z :=
    ((vectorField τ hτ hτT B (initialData D δ hδ (a • ξ) hs)).raw_smooth t).differentiable (by
      simp) z
  have hv := (hq.hasFDerivAt.comp_hasDerivAt z.2
    ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))).deriv
  change deriv (fun θ => q (z.1,θ)) z.2 = _ at hv
  have hd' : deriv (fun θ => a • (profile δ θ • canonicalVelocity τ hτ hτT B ξ hs t z.1)) z.2 =
      a • (deriv (profile δ) z.2 • canonicalVelocity τ hτ hτT B ξ hs t z.1) := hd.deriv
  rw [he,hd'] at hv
  simpa only [smul_smul] using hv.symm

theorem scaled_terminal_global_gradient (a k : ℝ) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space)
    (hY : HasFDerivAt Y (D.FInv.field t (Y x)) x) :
    fderiv ℝ (fun y => k⁻¹ • vector τ hτ hτT B (initialData D δ hδ (a • ξ) hs)
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) x =
      (a*deriv (profile δ) (k*⟪D.m₀,Y x⟫_ℝ)) •
        rankOne ℝ (canonicalVelocity τ hτ hτT B ξ hs t (Y x)) (D.normal.field t (Y x)) +
      slowGraphDerivative (fun z => vector τ hτ hτT B (initialData D δ hδ (a • ξ) hs) (t,z))
        k D.m₀ Y (D.FInv.field t (Y x)) x := by
  have hq := ((vectorField τ hτ hτT B (initialData D δ hδ (a • ξ) hs)).raw_smooth t).differentiable
    (by simp)
  have he := (graph_vector_hasFDerivAt
    (fun z => vector τ hτ hτT B (initialData D δ hδ (a • ξ) hs) (t,z))
    k hk D.m₀ Y _ x hY (hq _)).fderiv
  rw [scaled_terminal_angular_fderiv τ hτ hτT B δ hδ ξ hs] at he
  convert! he using 1
  apply congrArg (fun V : Space →L[ℝ] Space => V + _)
  apply ContinuousLinearMap.ext
  intro v
  simp only [smul_apply,rankOne_apply,smul_smul,graphMap_apply]
  rw [mul_comm]
  rfl

theorem scaled_terminal_global_gradient_bound (a k : ℝ) (hk : 0 < k)
    (R A C : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hG : (vectorField τ hτ hτT B (initialData D δ hδ (a • ξ) hs)).WordBound 6 R A 0)
    (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space)
    (hY : HasFDerivAt Y (D.FInv.field t (Y x)) x) (hJ : ‖D.FInv.field t (Y x)‖ ≤ C) :
    ‖fderiv ℝ (fun y => k⁻¹ • vector τ hτ hτT B (initialData D δ hδ (a • ξ) hs)
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) x -
      (a*deriv (profile δ) (k*⟪D.m₀,Y x⟫_ℝ)) •
        rankOne ℝ (canonicalVelocity τ hτ hτT B ξ hs t (Y x)) (D.normal.field t (Y x))‖ ≤
      (‖coordinateEquiv.symm.toContinuousLinearMap‖*(sobolevEmbeddingConstant period 3*A*R)*C)/k :=
        by
  rw [scaled_terminal_global_gradient τ hτ hτT B δ hδ ξ hs a k hk.ne' t Y x hY,
    add_sub_cancel_left]
  have hd := hG.raw_fderiv_le (by norm_num) t (graphMap k D.m₀ (Y x))
  simp only [majorant,Nat.add_zero,Nat.factorial_one,Nat.cast_one,pow_one,one_pow,mul_one] at hd
  have hn := slowGraphDerivative_norm_le
    (fun z => vector τ hτ hτT B (initialData D δ hδ (a • ξ) hs) (t,z))
    k D.m₀ Y (D.FInv.field t (Y x)) x
  have hb := sobolevEmbeddingConstant_nonneg period 3
  calc
    _ ≤ |k⁻¹| * ‖fderiv ℝ (fun z => vector τ hτ hτT B
          (initialData D δ hδ (a • ξ) hs) (t,z)) (graphMap k D.m₀ (Y x))‖ *
        ‖D.FInv.field t (Y x)‖ := hn
    _ ≤ |k⁻¹| * (‖coordinateEquiv.symm.toContinuousLinearMap‖*
        (sobolevEmbeddingConstant period 3*A*R)) * C :=
      mul_le_mul (mul_le_mul_of_nonneg_left hd (abs_nonneg _)) hJ (norm_nonneg _) (by positivity)
    _ = _ := by rw [abs_of_pos (inv_pos.mpr hk)]; ring

end EulerPacketPrimaryShear
