/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TransportPiolaFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.Laws
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SmoothField
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.PeriodicCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceGrad

/-! # RelativeError: periodicity of the transported Piola vector -/

@[expose] public section

noncomputable section

open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance

/-- The Piola vector formed from an inverse-flow Jacobian and a periodic
gradient remains lattice-periodic. -/
theorem inverseFlow_piolaVector_periodic
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    {f : Vec 2 → ℝ}
    (hper : IsZ2Periodic f) (t : ℝ) :
    IsZ2Periodic (fun x =>
      Matrix.mulVec
        (FaaDiBruno.flowMatrixCofactorTranspose
          (FaaDiBruno.spatialGradientMatrix (fun y => X 0 y t) x))
        (spaceGrad f (X 0 x t))) := by
  obtain ⟨L, _, hL⟩ := Infra.Flow.exists_global_spatial_lipschitz hb
  have hbper (r : ℝ) : IsZ2Periodic (b r) := by
    intro k x
    simpa using hb.periodic 0 k r x
  let Y : Vec 2 → Vec 2 := fun x => X 0 x t
  let q : Vec 2 → FaaDiBruno.FlowMatrix := fun x =>
    FaaDiBruno.flowMatrixCofactorTranspose
      (FaaDiBruno.spatialGradientMatrix Y x)
  have hYshift (k : Fin 2 → ℤ) :
      (fun x => Y (x + latticeShift k)) = fun x => Y x + latticeShift k := by
    funext x
    exact Infra.Flow.flow_lattice_equivariant b ⟨L, hL⟩ hbper hX x t 0 k
  have hD (k : Fin 2 → ℤ) (x : Vec 2) :
      fderiv ℝ Y (x + latticeShift k) = fderiv ℝ Y x := by
    calc
      fderiv ℝ Y (x + latticeShift k) =
          fderiv ℝ (fun z => Y (z + latticeShift k)) x := by
            rw [fderiv_comp_add_right]
      _ = fderiv ℝ (fun z => Y z + latticeShift k) x := by rw [hYshift k]
      _ = fderiv ℝ Y x := by rw [fderiv_add_const]
  have hq (k : Fin 2 → ℤ) (x : Vec 2) :
      q (x + latticeShift k) = q x := by
    dsimp [q]
    rw [show FaaDiBruno.spatialGradientMatrix Y (x + latticeShift k) =
        FaaDiBruno.spatialGradientMatrix Y x by
          ext i j
          simp only [FaaDiBruno.spatialGradientMatrix]
          exact congrArg (fun A : Vec 2 →L[ℝ] Vec 2 =>
            A (FaaDiBruno.coordinateVector 2 j) i) (hD k x)]
  have hgradper (i : Fin 2) :
      IsZ2Periodic (fun x => spaceGrad f x i) :=
    Infra.Classical.periodic_spaceGrad_component hper i
  intro k x
  change Matrix.mulVec (q (x + latticeShift k))
      (spaceGrad f (Y (x + latticeShift k))) =
    Matrix.mulVec (q x) (spaceGrad f (Y x))
  rw [show Y (x + latticeShift k) = Y x + latticeShift k from
    congrFun (hYshift k) x, hq k x]
  have hgradShift :
      spaceGrad f (Y x + latticeShift k) = spaceGrad f (Y x) := by
    ext i
    exact hgradper i k (Y x)
  rw [hgradShift]

end AVenhance.Infra.Section5.RelativeError

end
