/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TransportPiola
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointC3All
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2FlowIdentities

/-! # RelativeError: Piola data for the inverse flow -/

@[expose] public section

noncomputable section

open Homogenization
open AVenhance
open scoped ContDiff

namespace AVenhance.Infra.Section5.RelativeError

/-- A fixed inverse-flow map is jointly smooth in its spatial variable to
the order needed for the Piola transform. -/
theorem inverseFlow_contDiff_three
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X) (t : ℝ) :
    ContDiff ℝ 3 (fun z : Vec 2 => X 0 z t) := by
  have hInv := Infra.Flow.flow_inverse_joint_contDiff_three_all hb hX
  have hmap : ContDiff ℝ 3 (fun z : Vec 2 => (t, z, (0 : ℝ))) := by
    fun_prop
  change ContDiff ℝ 3 (fun z => X 0 z t)
  exact hInv.comp hmap

/-- The inverse flow Jacobian supplies both Piola identities: its cofactor
columns have zero divergence, and the cofactor times the inverse Jacobian is
the identity. -/
theorem inverseFlow_cofactorPiolaData
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    (hdiv : ∀ t x, vecDiv (b t) x = 0)
    (t : ℝ) (x : Vec 2) :
    let Y : Vec 2 → Vec 2 := fun z => X 0 z t
    (∀ j : Fin 2, ∑ i : Fin 2,
        (fderiv ℝ (fun z =>
          FaaDiBruno.flowMatrixCofactorTranspose
            (FaaDiBruno.spatialGradientMatrix Y z) i j) x)
          (basisVec i) = 0) ∧
    (∀ j k : Fin 2, ∑ i : Fin 2,
      FaaDiBruno.flowMatrixCofactorTranspose
          (FaaDiBruno.spatialGradientMatrix Y x) i j *
        (fderiv ℝ Y x (basisVec i)) k = if j = k then 1 else 0) := by
  dsimp only
  let Y : Vec 2 → Vec 2 := fun z => X 0 z t
  have hY3 : ContDiff ℝ 3 Y := inverseFlow_contDiff_three hb hX t
  have hY2 : ContDiff ℝ 2 Y := hY3.of_le (by norm_num)
  have hspatialDiv (s : ℝ) (z : Vec 2) :
      Infra.Flow.spatialDivergence b s z = 0 := by
    rw [Infra.Construction.spatialDivergence_eq_vecDiv hb]
    exact hdiv s z
  have hdet : (fderiv ℝ Y x).det = 1 :=
    Infra.Flow.flow_spatial_jacobian_det_eq_one_of_divergence_free
      hb hX hspatialDiv x t 0
  constructor
  · intro j
    exact cofactorTranspose_gradient_columns_divergence_free hY2 x j
  · exact cofactorTranspose_gradient_chain x hdet

/-- The forward Jacobian at the transported point is exactly the cofactor
matrix used in `inverseFlow_cofactorPiolaData`. -/
theorem inverseFlow_forwardJacobian_eq_cofactor
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    (hdiv : ∀ t x, vecDiv (b t) x = 0)
    (t : ℝ) (x : Vec 2) :
    FaaDiBruno.spatialGradientMatrix (fun y => X t y 0) (X 0 x t) =
      FaaDiBruno.flowMatrixCofactorTranspose
        (FaaDiBruno.spatialGradientMatrix (fun y => X 0 y t) x) := by
  have hspatialDiv (s : ℝ) (z : Vec 2) :
      Infra.Flow.spatialDivergence b s z = 0 := by
    rw [Infra.Construction.spatialDivergence_eq_vecDiv hb]
    exact hdiv s z
  exact FaaDiBruno.flow_spatialGradientMatrix_composed_inverse_eq_cofactor
    hb hX hspatialDiv t x

end AVenhance.Infra.Section5.RelativeError

end
