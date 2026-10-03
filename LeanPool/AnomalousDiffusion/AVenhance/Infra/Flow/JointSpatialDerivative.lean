/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SpatialC3
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SecondSpatial

/-! Joint continuity in target time and base point of the spatial derivative. -/

@[expose] public section

open Homogenization
open Set
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

/-- Coordinate basis used to identify matrices with spatial linear maps. -/
noncomputable def JointSpatialDerivative.flowSpatialBasis : Module.Basis (Fin 2) ℝ (Vec 2) :=
  Pi.basisFun ℝ (Fin 2)

/-- Continuous linear equivalence between two-by-two matrices and spatial endomorphisms. -/
noncomputable def JointSpatialDerivative.flowMatrixToSpatialCLM :
    Matrix (Fin 2) (Fin 2) ℝ ≃L[ℝ] (Vec 2 →L[ℝ] Vec 2) := by
  let e₀ : Matrix (Fin 2) (Fin 2) ℝ ≃ₗ[ℝ] (Vec 2 →ₗ[ℝ] Vec 2) :=
    Matrix.toLin JointSpatialDerivative.flowSpatialBasis JointSpatialDerivative.flowSpatialBasis
  let e₁ : (Vec 2 →ₗ[ℝ] Vec 2) ≃ₗ[ℝ] (Vec 2 →L[ℝ] Vec 2) :=
    LinearMap.toContinuousLinearMap
  let e : Matrix (Fin 2) (Fin 2) ℝ ≃ₗ[ℝ] (Vec 2 →L[ℝ] Vec 2) := e₀.trans e₁
  refine ⟨e, ?_, ?_⟩
  · exact e.toLinearMap.continuous_of_finiteDimensional
  · exact e.symm.toLinearMap.continuous_of_finiteDimensional

/-- On a forward compact target-time interval, the spatial derivative depends
jointly continuously on target time and base point, for fixed initial time. -/
theorem flow_spatialFDeriv_jointContinuousOn_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s t : ℝ) (hst : s ≤ t) :
    ContinuousOn (fun p : ℝ × Vec 2 => fderiv ℝ (fun z => X p.1 z s) p.2)
      (Icc s t ×ˢ univ) := by
  let J : ℝ × Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun p =>
    fderiv ℝ (fun z => X p.1 z s) p.2
  let M : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ := fun p =>
    JointSpatialDerivative.flowSpatialBasis.toMatrix (fun j => J p
        (JointSpatialDerivative.flowSpatialBasis j))
  have hentry (i j : Fin 2) :
      ContinuousOn (fun p : ℝ × Vec 2 => M p i j) (Icc s t ×ˢ univ) := by
    have hdir := flow_variational_direction_jointContinuous_of_le
      hb hX (JointSpatialDerivative.flowSpatialBasis j) s t hst
    have heval : Continuous (fun v : Vec 2 => v i) := continuous_apply i
    have hcoord : ContinuousOn
        (fun p : ℝ × Vec 2 => (J p (JointSpatialDerivative.flowSpatialBasis j)) i)
        (Icc s t ×ˢ univ) := heval.continuousOn.comp hdir (by
          intro p hp
          exact mem_univ (J p (JointSpatialDerivative.flowSpatialBasis j)))
    simpa [M, Module.Basis.toMatrix_apply, JointSpatialDerivative.flowSpatialBasis] using hcoord
  have hM : ContinuousOn M (Icc s t ×ˢ univ) := by
    apply continuousOn_pi.2
    intro i
    apply continuousOn_pi.2
    intro j
    exact hentry i j
  have hmatrix (p : ℝ × Vec 2) :
      M p = LinearMap.toMatrix JointSpatialDerivative.flowSpatialBasis
          JointSpatialDerivative.flowSpatialBasis
        (J p).toLinearMap := by
    ext i j
    simp [M, Module.Basis.toMatrix_apply, JointSpatialDerivative.flowSpatialBasis]
  have hrecover (p : ℝ × Vec 2) : JointSpatialDerivative.flowMatrixToSpatialCLM (M p) = J p := by
    ext v i
    dsimp [JointSpatialDerivative.flowMatrixToSpatialCLM]
    change (Matrix.toLin JointSpatialDerivative.flowSpatialBasis
        JointSpatialDerivative.flowSpatialBasis (M p) v) i = (J p v) i
    rw [hmatrix p, Matrix.toLin_toMatrix]
    rfl
  have hcont : ContinuousOn (fun p => JointSpatialDerivative.flowMatrixToSpatialCLM (M p))
      (Icc s t ×ˢ univ) :=
          JointSpatialDerivative.flowMatrixToSpatialCLM.continuous.comp_continuousOn hM
  exact hcont.congr fun p _ => (hrecover p).symm

end AVenhance.Infra.Flow
