/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointLabels
public import LeanPool.NavierStokesAndEuler.Euler.PacketNormalizedPrimary
public import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalInitialData
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryField
import LeanPool.NavierStokesAndEuler.Euler.Foundations.Lagrangian
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPiolaData
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryHistory

/-! The actual compact primary has exactly the source rank-one shear at
zero phase throughout its history interval, including the activation time.
No derivative of the finite-dimensional history is postulated. -/

@[expose] public section


noncomputable section

namespace EulerPacketPrimaryShear

open Set Filter InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLiftedGradientSpace EulerGraphPullback EulerPacketNormalizedPrimary
  EulerTransversePacketProvider EulerPacketTerminalDatum EulerTransversePacketPrimary
  EulerSpatialCutoffs EulerPeriodicProfile
open scoped ContDiff

theorem zero_slice_hasFDerivAt (A : Space × ℝ → Space) (x a : Space)
    (hA : DifferentiableAt ℝ A (x, 0)) (hzero : ∀ y, A (y, 0) = 0)
    (ha : HasDerivAt (fun θ : ℝ => A (x,θ)) a 0) :
    HasFDerivAt A ((toSpanSingleton ℝ a).comp (snd ℝ Space ℝ)) (x,0) := by
  have hs := hA.hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const (0 : ℝ) x))
  have he : (fun y => A (y,0)) = fun _ : Space => (0 : Space) := funext hzero
  change HasFDerivAt (fun y => A (y,0)) ((fderiv ℝ A (x,0)).comp (inl ℝ Space ℝ)) x at hs
  rw [he] at hs
  have hspace : ∀ v : Space, fderiv ℝ A (x,0) (v,0)=0 := by
    intro v
    have h := congrArg (fun L : Space →L[ℝ] Space => L v)
      (hs.unique (hasFDerivAt_const (0 : Space) x))
    exact h
  have ht := hA.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    ((hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id (0 : ℝ)))
  have hangle : fderiv ℝ A (x,0) (0,1)=a := ht.unique ha
  have hd : fderiv ℝ A (x,0) = (toSpanSingleton ℝ a).comp (snd ℝ Space ℝ) := by
    apply ContinuousLinearMap.ext
    rintro ⟨v,s⟩
    have hp : (v,s) = (v,(0 : ℝ))+s•((0 : Space),(1 : ℝ)) := by simp
    rw [hp,map_add,map_smul,hspace,hangle]
    simp
  exact hd ▸ hA.hasFDerivAt

theorem zero_phase_graph_hasFDerivAt (A : Space × ℝ → Space) (a m : Space)
    (hA : DifferentiableAt ℝ A (0, 0)) (hzero : ∀ y, A (y, 0) = 0)
    (ha : HasDerivAt (fun θ : ℝ => A (0,θ)) a 0) (c k : ℝ) :
    HasFDerivAt (fun y => c • A (y,k*⟪m,y⟫_ℝ)) ((c*k) • rankOne ℝ a m) 0 := by
  have hp : HasFDerivAt A ((toSpanSingleton ℝ a).comp (snd ℝ Space ℝ)) (graphMap k m 0) := by
    rw [map_zero]
    change HasFDerivAt A ((toSpanSingleton ℝ a).comp (snd ℝ Space ℝ)) (0,0)
    exact zero_slice_hasFDerivAt A 0 a hA hzero ha
  have h := (hp.comp 0 (graphMap k m).hasFDerivAt).const_smul c
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [smul_apply,comp_apply,toSpanSingleton_apply,coe_snd',graphMap_apply,
    rankOne_apply,smul_smul]
  congr 1
  ring

theorem rankOne_normalized (c : ℝ) (v m : Space) (hv : v ≠ 0) (hm : m ≠ 0) :
    c • rankOne ℝ v m =
      (c*(‖m‖*‖v‖)) • rankOne ℝ (unit v) (unit m) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [smul_apply,rankOne_apply,unit,real_inner_smul_left,smul_smul]
  congr 1
  field_simp [norm_ne_zero_iff.mpr hv,norm_ne_zero_iff.mpr hm]

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support)

/-- The literal leading primary on the physical phase graph in label coordinates. -/
def historyWave (α k : ℝ) (t : Icc (0 : ℝ) τ) (y : Space) : Space :=
  (α/k) • vector τ hτ hτT B (initialData D δ hδ ξ hs) (t,(y,k*⟪D.m₀,y⟫_ℝ))

theorem historyWave_hasFDerivAt (α k : ℝ) (hk : k ≠ 0) (t : Icc (0 : ℝ) τ) :
    HasFDerivAt (historyWave τ hτ hτT B δ hδ ξ hs α k t)
      ((α/δ) • rankOne ℝ (B.coefficients.labelVelocity 0 ξ t) D.m₀) 0 := by
  let A : Space × ℝ → Space := fun z =>
    vector τ hτ hτT B (initialData D δ hδ ξ hs) (t,z)
  have hA : DifferentiableAt ℝ A (0,0) :=
    ((vectorField τ hτ hτT B (initialData D δ hδ ξ hs)).raw_smooth
      ⟨t,t.property.1,t.property.2.trans hτT.le⟩).differentiable (by simp) (0,0)
  have hzero : ∀ y, A (y,0)=0 := by
    intro y
    change vector τ hτ hτT B (initialData D δ hδ ξ hs) (t,(y,0))=0
    rw [vector_compact_wave_history]
    simp [profile]
  have ha : HasDerivAt (fun θ : ℝ => A (0,θ)) (δ⁻¹ • B.coefficients.labelVelocity 0 ξ t) 0 := by
    simpa only [A,innerCutoff_zero,one_mul] using
      angular_derivative_zero_history τ hτ hτT B δ hδ ξ hs t 0
  have h := zero_phase_graph_hasFDerivAt A _ D.m₀ hA hzero ha (α/k) k
  have hc : α/k*k=α := by field_simp
  rw [hc] at h
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [smul_apply,rankOne_apply,smul_smul]
  congr 1
  rw [div_eq_mul_inv]
  ring

/-- The physical gradient uses the actual inverse Jacobian, producing the
normal F⁻ᵀm₀ rather than the initial direction m₀. -/
theorem historyWave_physical_hasFDerivAt (α k : ℝ) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) τ) (X Y : Space → Space)
    (hX : HasFDerivAt X (D.F.field ⟨t, t.property.1, t.property.2.trans hτT.le⟩ 0) 0)
    (hY : DifferentiableAt ℝ Y (X 0)) (hleft : ∀ y, Y (X y) = y) :
    HasFDerivAt (fun x => historyWave τ hτ hτT B δ hδ ξ hs α k t (Y x))
      ((α/δ) • rankOne ℝ (B.coefficients.labelVelocity 0 ξ t)
        (D.normal.field ⟨t,t.property.1,t.property.2.trans hτT.le⟩ 0)) (X 0) := by
  let tg : Icc (0 : ℝ) D.T := ⟨t,t.property.1,t.property.2.trans hτT.le⟩
  have he : (Y ∘ X) = id := funext hleft
  have hdY := EulerLagrangian.derivative_pullback_inverse Y X (D.deformationEquiv tg 0) 0 hX hY
  rw [he,fderiv_id,id_comp] at hdY
  have hy : HasFDerivAt Y (D.deformationEquiv tg 0).symm.toContinuousLinearMap (X 0) :=
    hdY ▸ hY.hasFDerivAt
  have hp : HasFDerivAt (historyWave τ hτ hτT B δ hδ ξ hs α k t)
      ((α/δ) • rankOne ℝ (B.coefficients.labelVelocity 0 ξ t) D.m₀) (Y (X 0)) := by
    rw [hleft]
    exact historyWave_hasFDerivAt τ hτ hτT B δ hδ ξ hs α k hk t
  convert! hp.comp (X 0) hy using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [smul_apply,comp_apply,rankOne_apply]
  congr 2
  exact (D.FInv.field tg 0).adjoint_inner_left v D.m₀

theorem historyWave_physical_norm (α k : ℝ) (hα : 0 ≤ α) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) τ) (X Y : Space → Space)
    (hX : HasFDerivAt X (D.F.field ⟨t, t.property.1, t.property.2.trans hτT.le⟩ 0) 0)
    (hY : DifferentiableAt ℝ Y (X 0)) (hleft : ∀ y, Y (X y) = y) :
    ‖fderiv ℝ (fun x => historyWave τ hτ hτT B δ hδ ξ hs α k t (Y x)) (X 0)‖ =
      (α/δ) * (‖B.coefficients.labelVelocity 0 ξ t‖ *
        ‖D.normal.field ⟨t,t.property.1,t.property.2.trans hτT.le⟩ 0‖) := by
  rw [(historyWave_physical_hasFDerivAt τ hτ hτT B δ hδ ξ hs α k hk t X Y hX hY hleft).fderiv,
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hα hδ.le),norm_rankOne]

end EulerPacketPrimaryShear
