/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PhysicalGraphTimeFields
public import LeanPool.NavierStokesAndEuler.Euler.ChildParticleJacobian

@[expose] public section

/-! Initial identity and determinant one for the actual child coefficient
map. These invariants pass directly to the next parent coefficient data. -/

noncomputable section

namespace EulerPhysicalGraphFlowBounds.Data

open Set EulerLiftedGradientSpace EulerSmoothBanachFlow EulerGraphInvariantFlow

variable {P T : ℝ} [Fact (0 < P)] (G : EulerPhysicalGraphFlowBounds.Data P T)
  (k : ℝ) (m : Vector3) (ell : ℝ)

theorem physicalDisplacementCoefficient_zero (x : Vector3) :
    (G.physicalDisplacementCoefficient k m ell).field ⟨0,le_rfl,G.time_nonneg⟩ x=0 := by
  rw [physicalDisplacementCoefficient,physicalCoefficient_apply,G.coverDisplacementCoefficient_apply]
  simp only [(flowData T G.time_nonneg G.A).forward_zero,sub_self,Prod.fst_zero,smul_zero]

theorem physicalDisplacementCoefficient_det_one
    (hgraph : ∀ t z, graphConstraint k m (G.A.field t z)=0) (hell : 0 < ell)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    (ContinuousLinearMap.id ℝ Vector3 +
      fderiv ℝ ((G.physicalDisplacementCoefficient k m ell).field t : Vector3 → Vector3) x).det=1
        := by
  let C := G.physicalDisplacementCoefficient k m ell
  have he : (fun y => y+C.field t y) =
      (flowData T G.time_nonneg (physicalCoefficient k m T G.A ell)).forward t := by
    funext y
    change y+(G.physicalDisplacementCoefficient k m ell).field t y=_
    rw [G.physicalDisplacementCoefficient_eq k m ell hell,
      G.displacementField_eq k m hgraph ell hell,displacement_eq]
    abel
  have hj : fderiv ℝ (fun y => y+C.field t y) x =
      ContinuousLinearMap.id ℝ Vector3 + fderiv ℝ (C.field t : Vector3 → Vector3) x :=
    ((hasFDerivAt_id x).add ((C.smooth t).differentiable (by simp) x).hasFDerivAt).fderiv
  rw [he] at hj
  change (ContinuousLinearMap.id ℝ Vector3 + fderiv ℝ (C.field t : Vector3 → Vector3) x).det=1
  rw [← hj]
  exact forward_det_one T G.time_nonneg (physicalCoefficient k m T G.A ell)
    (physicalCoefficient_trace_zero k m T G.A hgraph G.divergence ell hell.ne') t x

theorem childDisplacementCoefficient_zero
    (PD : SmoothTimeField (Icc (0 : ℝ) T) Vector3 Vector3)
    (hPD : ∀ x, PD.field ⟨0,le_rfl,G.time_nonneg⟩ x=0) (x : Vector3) :
    (EulerChildParticleTime.displacement PD (G.physicalDisplacementCoefficient k m ell)).field
      ⟨0,le_rfl,G.time_nonneg⟩ x=0 := by
  rw [EulerChildParticleTime.displacement_apply,G.physicalDisplacementCoefficient_zero,
    add_zero,hPD]

theorem childDisplacementCoefficient_det_one
    (hgraph : ∀ t z, graphConstraint k m (G.A.field t z)=0) (hell : 0 < ell)
    (PD : SmoothTimeField (Icc (0 : ℝ) T) Vector3 Vector3)
    (hPD : ∀ t x, (ContinuousLinearMap.id ℝ Vector3 +
      fderiv ℝ (PD.field t : Vector3 → Vector3) x).det=1)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    (ContinuousLinearMap.id ℝ Vector3 +
      fderiv ℝ
        ((EulerChildParticleTime.displacement PD (G.physicalDisplacementCoefficient k m ell)).field
          t :
          Vector3 → Vector3) x).det=1 :=
  EulerChildParticleTime.displacement_det_one PD (G.physicalDisplacementCoefficient k m ell) t
    (hPD t) (G.physicalDisplacementCoefficient_det_one k m ell hgraph hell t) x

end EulerPhysicalGraphFlowBounds.Data
