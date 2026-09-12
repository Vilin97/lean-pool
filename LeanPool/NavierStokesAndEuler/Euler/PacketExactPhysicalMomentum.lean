/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.ExactLiftedGraphPressure
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalEulerTransform
import LeanPool.NavierStokesAndEuler.Euler.PacketExactSourceEquation
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! The constructed exact lifted packet gives the actual momentum equation
after the genuine parent-flow change of coordinates. The scalar pressure
is the normalized radial potential of the constructed pressure tower. -/

section

/-! The frame evolution is derived by differentiating the actual parent
flow. Symmetry of the genuine second derivative supplies the mixed-derivative
identity; no independent strain evolution is assumed. -/

@[expose] public section

noncomputable section

namespace EulerPacketPhysicalTransform

open Set Filter InnerProductSpace ContinuousLinearMap EulerLagrangian
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem flow_time_derivative_eq (X u : ℝ × E → E) (q : ℝ × E)
    (hX : DifferentiableAt ℝ X q)
    (hflow : HasDerivAt (fun s => X (s, q.2)) (u (q.1, X q)) q.1) :
    fderiv ℝ X q (1,0) = u (q.1,X q) := by
  have h := hX.hasFDerivAt.comp_hasDerivAt q.1
    ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))
  exact h.unique hflow

omit [CompleteSpace E] in
theorem parent_frame_time (X u : ℝ × E → E) (F : ℝ × E → E →L[ℝ] E)
    (q : ℝ × E) (DF : (ℝ × E) →L[ℝ] (E →L[ℝ] E)) (Du : (ℝ × E) →L[ℝ] E)
    (hX : ContDiffAt ℝ 2 X q) (hF : HasFDerivAt F DF q)
    (hu : HasFDerivAt u Du (q.1, X q))
    (hframe : F =ᶠ[𝓝 q] fun r => (fderiv ℝ X r).comp (inr ℝ ℝ E))
    (hflow : (fun r => fderiv ℝ X r (1, 0)) =ᶠ[𝓝 q] fun r => u (r.1, X r))
    (v : E) : DF (1,0) v = Du (0,F q v) := by
  have hDX : DifferentiableAt ℝ (fderiv ℝ X) q :=
    (hX.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  have hFv := hF.clm_apply (hasFDerivAt_const v q)
  have hDXv := hDX.hasFDerivAt.clm_apply (hasFDerivAt_const ((0 : ℝ),v) q)
  have hv : (fun r => F r v) =ᶠ[𝓝 q] fun r => fderiv ℝ X r (0,v) := by
    filter_upwards [hframe] with r hr
    rw [hr]
    rfl
  have he := hv.fderiv_eq (𝕜 := ℝ)
  rw [hFv.fderiv,hDXv.fderiv] at he
  have hfirst : DF (1,0) v = fderiv ℝ (fderiv ℝ X) q (1,0) (0,v) := by
    have h := congrArg (fun L : (ℝ × E) →L[ℝ] E => L (1,0)) he
    simpa only [add_apply,comp_apply,zero_apply,map_zero,zero_add,flip_apply] using h
  have hDXt := hDX.hasFDerivAt.clm_apply (hasFDerivAt_const ((1 : ℝ),(0 : E)) q)
  have hUX := hu.comp q ((hasFDerivAt_fst).prodMk (hX.differentiableAt two_ne_zero).hasFDerivAt)
  change HasFDerivAt (fun r => u (r.1,X r)) _ q at hUX
  have het := hflow.fderiv_eq (𝕜 := ℝ)
  rw [hDXt.fderiv,hUX.fderiv] at het
  have hsecond : fderiv ℝ (fderiv ℝ X) q (0,v) (1,0) = Du (0,F q v) := by
    have h := congrArg (fun L : (ℝ × E) →L[ℝ] E => L (0,v)) het
    have hfq := congrArg (fun L : E →L[ℝ] E => L v) hframe.eq_of_nhds
    simp only [comp_apply,inr_apply] at hfq
    simpa only [add_apply,comp_apply,zero_apply,map_zero,zero_add,flip_apply,prod_apply,
      coe_fst',← hfq] using h
  exact hfirst.trans (((hX.isSymmSndFDerivAt (by simp)).eq (1,0) (0,v)).trans hsecond)

/-- The usual flow ODE and Jacobian identity suffice to supply the frame
evolution used by the physical Euler transformation. The identities need
only hold in a neighborhood of the current interior spacetime point. -/
theorem physical_euler_momentum_of_flow
    (κ k : ℝ) (hκ : k * κ = 1) (m : E)
    (F : ℝ × E → E →L[ℝ] E) (z : ℝ × (E × ℝ) → E)
    (u : ℝ × E → E) (p Q : ℝ × E → ℝ) (X Y : ℝ × E → E)
    (t : ℝ) (x : E) (A : E ≃L[ℝ] E)
    (DF : (ℝ × E) →L[ℝ] (E →L[ℝ] E)) (Dz : (ℝ × (E × ℝ)) →L[ℝ] E)
    (Du : (ℝ × E) →L[ℝ] E) (P : E)
    (hleft : ∀ s y, Y (s, X (s, y)) = y)
    (hY : DifferentiableAt ℝ (inverseCoordinates Y) (t, X (t, x)))
    (hX : ContDiffAt ℝ 2 X (t, x))
    (hframe : F =ᶠ[𝓝 (t, x)] fun r => (fderiv ℝ X r).comp (inr ℝ ℝ E))
    (hflow : (fun r => fderiv ℝ X r (1, 0)) =ᶠ[𝓝 (t, x)] fun r => u (r.1, X r))
    (hF : HasFDerivAt F DF (t, x)) (hz : HasFDerivAt z Dz (spaceTimeGraph k m (t, x)))
    (hA : F (t, x) = A.toContinuousLinearMap)
    (hu : HasFDerivAt u Du (t, X (t, x)))
    (hp : DifferentiableAt ℝ (fun y => p (t, y)) (X (t, x)))
    (hQ : DifferentiableAt ℝ (fun y => Q (t, y)) x)
    (hQgradient : gradient (fun y => Q (t, y)) x = κ • P)
    (hparent : momentumResidual u p (t, X (t, x)) = 0)
    (hlift : Dz (1, (0, 0)) +
      (2 : ℝ) • A.symm (DF (1, 0) (z (spaceTimeGraph k m (t, x)))) +
      Dz (0, (κ • z (spaceTimeGraph k m (t, x)), ⟪m, z (spaceTimeGraph k m (t, x))⟫_ℝ)) +
      κ • A.symm (DF (0, z (spaceTimeGraph k m (t, x))) (z (spaceTimeGraph k m (t, x)))) +
      A.symm (A.symm.toContinuousLinearMap.adjoint P) = 0) :
    momentumResidual (fun q => u q+physicalVelocity κ k m F z Y q)
      (fun q => p q+physicalPressure Q Y q) (t,X (t,x)) = 0 := by
  have hXt : HasDerivAt (fun s => X (s,x)) (u (t,X (t,x))) t := by
    have h := (hX.differentiableAt two_ne_zero).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
    rw [hflow.eq_of_nhds] at h
    exact h
  have hXs : HasFDerivAt (fun y => X (t,y)) A.toContinuousLinearMap x := by
    have h := (hX.differentiableAt two_ne_zero).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
    change HasFDerivAt (fun y => X (t,y)) ((fderiv ℝ X (t,x)).comp (inr ℝ ℝ E)) x at h
    rw [← hframe.eq_of_nhds,hA] at h
    exact h
  have hstrain (v : E) : Du (0,v) = DF (1,0) (A.symm v) := by
    have h := parent_frame_time X u F (t,x) DF Du hX hF hu hframe hflow (A.symm v)
    simpa only [hA,ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply] using
        h.symm
  exact physical_euler_momentum κ k hκ m F z u p Q X Y t x A DF Dz Du P
    hleft hY hXt hXs hF hz hA hu hp hQ hstrain hQgradient hparent hlift

end EulerPacketPhysicalTransform

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketPhysicalTransform

open Set Filter InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection
  EulerPacketCorrectionCoefficients EulerLagrangian
open scoped Topology ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) {P : ℝ} [Fact (0 < P)]
  {κ : ℝ} {hκ : |κ| ≤ 1} {Z R : FieldTower P D.T}
  {B : Budget P D.T_pos (correctionData D P κ hκ Z R)}
  (S : ExactLiftedPacket P D.T_pos (correctionData D P κ hκ Z R) B)

/-- All derivatives and the pressure of the perturbation are constructed
from the exact lifted solution. Only the actual parent flow and its inverse
enter as geometric data. -/
theorem exact_source_momentum
    (k : ℝ) (hk : k * κ = 1)
    (F : ℝ × Space → Space →L[ℝ] Space)
    (u : ℝ × Space → Space) (p : ℝ × Space → ℝ) (X Y : ℝ × Space → Space)
    (hmatch : ∀ s : Icc (0 : ℝ) D.T, ∀ y, F (s,y) = D.F.field s y)
    (t : ℝ) (ht : t ∈ Ioo 0 D.T) (x : Space)
    (hleft : ∀ s y, Y (s,X (s,y)) = y)
    (hY : DifferentiableAt ℝ (inverseCoordinates Y) (t,X (t,x)))
    (hX : ContDiffAt ℝ 2 X (t,x))
    (hframe : F =ᶠ[𝓝 (t,x)] fun r => (fderiv ℝ X r).comp (inr ℝ ℝ Space))
    (hflow : (fun r => fderiv ℝ X r (1,0)) =ᶠ[𝓝 (t,x)] fun r => u (r.1,X r))
    (hu : DifferentiableAt ℝ u (t,X (t,x)))
    (hp : DifferentiableAt ℝ (fun y => p (t,y)) (X (t,x)))
    (hparent : momentumResidual u p (t,X (t,x)) = 0) :
    momentumResidual (fun q => u q+physicalVelocity κ k D.m₀ F S.rawVelocity Y q)
      (fun q => p q+physicalPressure (S.rawGraphPotential k) Y q) (t,X (t,x)) = 0 := by
  have hDF : DifferentiableAt ℝ (fun r => (fderiv ℝ X r).comp (inr ℝ ℝ Space)) (t,x) :=
    ((hX.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero).clm_comp
      (differentiableAt_const (inr ℝ ℝ Space))
  have hF : HasFDerivAt F (fderiv ℝ F (t,x)) (t,x) :=
    (hDF.congr_of_eventuallyEq hframe).hasFDerivAt
  have hz : HasFDerivAt S.rawVelocity
      (fderiv ℝ S.rawVelocity (spaceTimeGraph k D.m₀ (t,x)))
      (spaceTimeGraph k D.m₀ (t,x)) :=
    (S.rawVelocity_hasFDerivAt t ht (x,k*⟪D.m₀,x⟫_ℝ)).differentiableAt.hasFDerivAt
  have hA : F (t,x) = (D.deformationEquiv ⟨t,ht.1.le,ht.2.le⟩ x).toContinuousLinearMap :=
    hmatch ⟨t,ht.1.le,ht.2.le⟩ x
  exact physical_euler_momentum_of_flow κ k hk D.m₀ F S.rawVelocity u p
    (S.rawGraphPotential k) X Y t x (D.deformationEquiv ⟨t,ht.1.le,ht.2.le⟩ x)
    (fderiv ℝ F (t,x)) (fderiv ℝ S.rawVelocity (spaceTimeGraph k D.m₀ (t,x)))
    (fderiv ℝ u (t,X (t,x))) (S.rawPressure (spaceTimeGraph k D.m₀ (t,x)))
    hleft hY hX hframe hflow hF hz hA hu.hasFDerivAt hp
    ((S.rawGraphPotential_smooth k hk t).differentiable (by simp) x)
    (S.rawGraphPotential_gradient k hk t x) hparent
    (S.source_equation_of_frame D F hmatch t ht (x,k*⟪D.m₀,x⟫_ℝ) _ hF)

end EulerPacketPhysicalTransform
