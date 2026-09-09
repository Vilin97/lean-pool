/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryFactorization
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryShearIdentity

@[expose] public section

/-! Exact rank-one primary shear throughout the joined history and forward
interval, obtained from the proved factorization of the actual primary. -/

noncomputable section

namespace EulerPacketPrimaryShear

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLiftedGradientSpace EulerGraphPullback EulerPacketNormalizedPrimary
  EulerTransversePacketProvider EulerPacketTerminalDatum EulerTransversePacketPrimary
  EulerSpatialCutoffs EulerPeriodicProfile EulerPacketPrimaryFactorization
open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support)

def fullWave (α k : ℝ) (t : Icc (0 : ℝ) D.T) (y : Space) : Space :=
  (α/k) • vector τ hτ hτT B (initialData D δ hδ ξ hs) (t,(y,k*⟪D.m₀,y⟫_ℝ))

theorem fullWave_hasFDerivAt (α k : ℝ) (hk : k ≠ 0) (t : Icc (0 : ℝ) D.T) :
    HasFDerivAt (fullWave τ hτ hτT B δ hδ ξ hs α k t)
      ((α/δ) • rankOne ℝ (envelopedVelocity τ hτ hτT B δ hδ ξ hs t 0) D.m₀) 0 := by
  let A : Space × ℝ → Space := fun z =>
    vector τ hτ hτT B (initialData D δ hδ ξ hs) (t,z)
  have hA : DifferentiableAt ℝ A (0,0) :=
    ((vectorField τ hτ hτT B (initialData D δ hδ ξ hs)).raw_smooth t).differentiable (by simp) (0,0)
  have hzero : ∀ y, A (y,0)=0 := by
    intro y
    change vector τ hτ hτT B (initialData D δ hδ ξ hs) (t,(y,0))=0
    rw [vector_factorization]
    simp [profile]
  have ha : HasDerivAt (fun θ : ℝ => A (0,θ))
      (δ⁻¹ • envelopedVelocity τ hτ hτT B δ hδ ξ hs t 0) 0 := by
    have hp := (profile_hasDerivAt δ hδ 0).differentiableAt.hasDerivAt
    rw [profile_deriv_zero δ hδ] at hp
    have he : (fun θ : ℝ => A (0,θ)) =
        fun θ => profile δ θ • envelopedVelocity τ hτ hτT B δ hδ ξ hs t 0 :=
      funext (vector_factorization τ hτ hτT B δ hδ ξ hs t 0)
    rw [he]
    exact hp.smul_const _
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

theorem fullWave_physical_hasFDerivAt (α k : ℝ) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) D.T) (X Y : Space → Space)
    (hX : HasFDerivAt X (D.F.field t 0) 0)
    (hY : DifferentiableAt ℝ Y (X 0)) (hleft : ∀ y, Y (X y)=y) :
    HasFDerivAt (fun x => fullWave τ hτ hτT B δ hδ ξ hs α k t (Y x))
      ((α/δ) • rankOne ℝ (envelopedVelocity τ hτ hτT B δ hδ ξ hs t 0)
        (D.normal.field t 0)) (X 0) := by
  have he : (Y ∘ X) = id := funext hleft
  have hdY := EulerLagrangian.derivative_pullback_inverse Y X (D.deformationEquiv t 0) 0 hX hY
  rw [he,fderiv_id,id_comp] at hdY
  have hy : HasFDerivAt Y (D.deformationEquiv t 0).symm.toContinuousLinearMap (X 0) :=
    hdY ▸ hY.hasFDerivAt
  have hp : HasFDerivAt (fullWave τ hτ hτT B δ hδ ξ hs α k t)
      ((α/δ) • rankOne ℝ (envelopedVelocity τ hτ hτT B δ hδ ξ hs t 0) D.m₀) (Y (X 0)) := by
    rw [hleft]
    exact fullWave_hasFDerivAt τ hτ hτT B δ hδ ξ hs α k hk t
  convert! hp.comp (X 0) hy using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [smul_apply,comp_apply,rankOne_apply]
  congr 2
  exact (D.FInv.field t 0).adjoint_inner_left v D.m₀

theorem fullWave_physical_norm (α k : ℝ) (hα : 0 ≤ α) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) D.T) (X Y : Space → Space)
    (hX : HasFDerivAt X (D.F.field t 0) 0)
    (hY : DifferentiableAt ℝ Y (X 0)) (hleft : ∀ y, Y (X y)=y) :
    ‖fderiv ℝ (fun x => fullWave τ hτ hτT B δ hδ ξ hs α k t (Y x)) (X 0)‖ =
      (α/δ) * (‖D.normal.field t 0‖ * ‖envelopedVelocity τ hτ hτT B δ hδ ξ hs t 0‖) := by
  rw [(fullWave_physical_hasFDerivAt τ hτ hτT B δ hδ ξ hs α k hk t X Y hX hY hleft).fderiv,
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hα hδ.le),norm_rankOne,mul_comm
      ‖envelopedVelocity τ hτ hτT B δ hδ ξ hs t 0‖ ‖D.normal.field t 0‖]

/-- The normalized rank-one expression is exactly the one in the source
geometry record, with c=α/δ and the actual primary velocity. -/
theorem fullWave_physical_normalized_gradient (α k : ℝ) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) D.T) (X Y : Space → Space)
    (hX : HasFDerivAt X (D.F.field t 0) 0)
    (hY : DifferentiableAt ℝ Y (X 0)) (hleft : ∀ y, Y (X y)=y)
    (hv : envelopedVelocity τ hτ hτT B δ hδ ξ hs t 0 ≠ 0) :
    fderiv ℝ (fun x => fullWave τ hτ hτT B δ hδ ξ hs α k t (Y x)) (X 0) =
      ((α/δ)*(‖D.normal.field t 0‖*‖envelopedVelocity τ hτ hτT B δ hδ ξ hs t 0‖)) •
        rankOne ℝ (unit (envelopedVelocity τ hτ hτT B δ hδ ξ hs t 0)) (unit (D.normal.field t 0))
          := by
  rw [(fullWave_physical_hasFDerivAt τ hτ hτT B δ hδ ξ hs α k hk t X Y hX hY hleft).fderiv]
  exact rankOne_normalized _ _ _ hv (HistoryData.normal_ne_zero t 0)

theorem fullWave_physical_canonical_gradient (α k : ℝ) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) D.T) (X Y : Space → Space)
    (hX : HasFDerivAt X (D.F.field t 0) 0)
    (hY : DifferentiableAt ℝ Y (X 0)) (hleft : ∀ y, Y (X y)=y) :
    fderiv ℝ (fun x => fullWave τ hτ hτT B δ hδ ξ hs α k t (Y x)) (X 0) =
      (α/δ) • rankOne ℝ (canonicalVelocity τ hτ hτT B ξ hs t 0) (D.normal.field t 0) := by
  rw [(fullWave_physical_hasFDerivAt τ hτ hτT B δ hδ ξ hs α k hk t X Y hX hY hleft).fderiv,
    envelopedVelocity_independent_profile τ hτ hτT B δ 1 hδ zero_lt_one]
  rfl

theorem fullWave_physical_canonical_norm (α k : ℝ) (hα : 0 ≤ α) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) D.T) (X Y : Space → Space)
    (hX : HasFDerivAt X (D.F.field t 0) 0)
    (hY : DifferentiableAt ℝ Y (X 0)) (hleft : ∀ y, Y (X y)=y) :
    ‖fderiv ℝ (fun x => fullWave τ hτ hτT B δ hδ ξ hs α k t (Y x)) (X 0)‖ =
      (α/δ) * (‖D.normal.field t 0‖ * ‖canonicalVelocity τ hτ hτT B ξ hs t 0‖) := by
  rw [fullWave_physical_norm τ hτ hτT B δ hδ ξ hs α k hα hk t X Y hX hY hleft,
    envelopedVelocity_independent_profile τ hτ hτT B δ 1 hδ zero_lt_one]
  rfl

/-- The source amplitude choice gives exactly the requested center shear
for the genuine primary, at any chosen target time. The size in this
choice uses the velocity independent of the narrow profile δ. -/
theorem fullWave_target_shear (h k : ℝ) (hh : 0 ≤ h) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) D.T) (X Y : Space → Space)
    (hX : HasFDerivAt X (D.F.field t 0) 0)
    (hY : DifferentiableAt ℝ Y (X 0)) (hleft : ∀ y, Y (X y)=y)
    (hv : canonicalVelocity τ hτ hτT B ξ hs t 0 ≠ 0) :
    ‖fderiv ℝ (fun x => fullWave τ hτ hτT B δ hδ ξ hs
      (δ*h/(‖D.normal.field t 0‖*‖canonicalVelocity τ hτ hτT B ξ hs t 0‖)) k t (Y x)) (X 0)‖ = h :=
        by
  have hm : ‖D.normal.field t 0‖ ≠ 0 := norm_ne_zero_iff.mpr (HistoryData.normal_ne_zero t 0)
  have hw : ‖canonicalVelocity τ hτ hτT B ξ hs t 0‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  rw [fullWave_physical_canonical_norm τ hτ hτT B δ hδ ξ hs _ k
    (div_nonneg (mul_nonneg hδ.le hh) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    hk t X Y hX hY hleft]
  field_simp [hδ.ne',hm,hw]

end EulerPacketPrimaryShear
