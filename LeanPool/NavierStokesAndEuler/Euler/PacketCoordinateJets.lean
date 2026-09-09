/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceCorrectionCoefficients
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketTimeData
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderFullTime

/-! Genuine time and spatial derivatives of z = k F⁻¹ W.  The inverse
derivative is derived from the prescribed deformation, including at the
endpoints of the actual time interval. -/

@[expose] public section


noncomputable section

namespace EulerPacketCoordinates

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerPacketPointJets EulerPacketProfileRecursion EulerPacketCylinderField
  EulerPacketCorrectionCoefficients EulerTransversePacketProvider
  EulerVolterraConvolution EulerLpCylinderRectangular
open scoped ContDiff

/-- Cache the standard `NormedAddCommGroup Space` instance to shorten typeclass synthesis. -/
local instance instPacketCoordinateJets1 : NormedAddCommGroup Space := inferInstance
/-- Cache the standard `NormedSpace ℝ Space` instance to shorten typeclass synthesis. -/
local instance instPacketCoordinateJets2 : NormedSpace ℝ Space := inferInstance

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : Data U)

/-- Coordinate, defined pointwise by `k • rawInverse D z (W z)`. -/
def coordinate (k : ℝ) (W : VectorField) : VectorField :=
  fun z => k • rawInverse D z (W z)

/-- Inverse time, given by `D.inverseDerivative (D.clamp z.1) z.2.1`. -/
def inverseTime (z : Domain) : Space →L[ℝ] Space :=
  D.inverseDerivative (D.clamp z.1) z.2.1

/-- Inverse time coefficient, bundling `path`, `orbit`, `raw_eq`. -/
def inverseTimeCoefficient : MatrixCoefficient D.T (inverseTime D) where
  path := D.inverseDerivative
  orbit := D.inverseDerivative_orbit
  raw_eq t x θ := by simp only [inverseTime,Data.clamp_coe]

/-- Coordinate time, defined pointwise by `k • (inverseTime D z (W z) + rawInverse D z (Wt z))`. -/
def coordinateTime (k : ℝ) (W Wt : VectorField) : VectorField :=
  fun z => k • (inverseTime D z (W z) + rawInverse D z (Wt z))

theorem coordinateTime_formula (k : ℝ) (W Wt : VectorField) (z : Domain) :
    coordinateTime D k W Wt z =
      k • (rawInverse D z (Wt z) - rawInverse D z (D.strain z (W z))) := by
  change k • (-rawInverse D z (D.strain z (W z)) + rawInverse D z (Wt z)) = _
  congr 1
  abel

theorem frame_coordinate (k : ℝ) (W : VectorField) (z : Domain) :
    rawFrame D z (coordinate D k W z) = k • W z := by
  simp only [coordinate,rawFrame,rawInverse,map_smul,D.inverse_right]

theorem reconstruct (k : ℝ) (hk : k ≠ 0) (W : VectorField) (z : Domain) :
    W z = k⁻¹ • rawFrame D z (coordinate D k W z) := by
  rw [frame_coordinate,smul_smul,inv_mul_cancel₀ hk,one_smul]

theorem normal_coordinate (k : ℝ) (W : VectorField) (z : Domain) :
    ⟪D.m₀,coordinate D k W z⟫_ℝ = k*⟪D.normalField z,W z⟫_ℝ := by
  change ⟪D.m₀,k • rawInverse D z (W z)⟫_ℝ =
    k*⟪(rawInverse D z).adjoint D.m₀,W z⟫_ℝ
  rw [inner_smul_right,adjoint_inner_left]

theorem coordinate_hasDerivWithinAt (k : ℝ) (W Wt : VectorField)
    (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ)
    (hW : HasDerivWithinAt (fun r => W (r, (x, θ))) (Wt (t, (x, θ)))
      (Icc (0 : ℝ) D.T) t) :
    HasDerivWithinAt (fun r => coordinate D k W (r,(x,θ)))
      (coordinateTime D k W Wt (t,(x,θ))) (Icc (0 : ℝ) D.T) t := by
  have hi := D.inverse_hasDerivWithinAt t t.property x
  have h := (hi.clm_apply hW).const_smul k
  convert! h using 1

theorem coordinate_derivWithin (k : ℝ) (W Wt : VectorField)
    (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ)
    (hW : HasDerivWithinAt (fun r => W (r, (x, θ))) (Wt (t, (x, θ)))
      (Icc (0 : ℝ) D.T) t) :
    derivWithin (fun r => coordinate D k W (r,(x,θ))) (Icc (0 : ℝ) D.T) t =
      coordinateTime D k W Wt (t,(x,θ)) :=
  (coordinate_hasDerivWithinAt D k W Wt t x θ hW).derivWithin
    ((uniqueDiffOn_Icc D.T_pos) _ t.property)

section Fields

variable {P : ℝ} [Fact (0 < P)] {W Wt : VectorField}
  (G : Field P D.T W) (Gt : Field P D.T Wt)

/-- Coordinate field, given by `((inverseCoefficient D).multiply G).smul k`. -/
def coordinateField (k : ℝ) : Field P D.T (coordinate D k W) :=
  ((inverseCoefficient D).multiply G).smul k

/-- Coordinate time field, given by `(((inverseTimeCoefficient D).multiply G).add
((inverseCoefficient D).multiply Gt)).smul k`. -/
def coordinateTimeField (k : ℝ) : Field P D.T (coordinateTime D k W Wt) :=
  (((inverseTimeCoefficient D).multiply G).add ((inverseCoefficient D).multiply Gt)).smul k

theorem coordinateField_time (k : ℝ) (hW : TimeDerivative D.T_pos.le G Gt) :
    TimeDerivative D.T_pos.le (coordinateField D G k) (coordinateTimeField D G Gt k) := by
  intro t
  have h := (fullProduct_hasDerivWithinAt P D.T D.T_pos.le D.FInv.field D.inverseDerivative
    D.inverse_hasDerivWithinAt G.path Gt.path hW t).const_smul k
  exact h

include G in
theorem coordinate_smooth (k : ℝ) (t : Icc (0 : ℝ) D.T) :
    ContDiff ℝ ∞ (fun y : SpatialDomain => coordinate D k W (t,y)) :=
  (coordinateField D G k).raw_smooth t

include G in
theorem normalized_spatial_derivative (k : ℝ) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) (v : SpatialDomain) :
    k • rawInverse D (t,(x,θ)) (fderiv ℝ (fun y => W (t,y)) (x,θ) v) =
      rawInverse D (t,(x,θ))
        (fderiv ℝ (D.F.field t : Space → Space →L[ℝ] Space) x v.1
          (coordinate D k W (t,(x,θ)))) +
        fderiv ℝ (fun y => coordinate D k W (t,y)) (x,θ) v := by
  have hfst : HasFDerivAt (fun y : SpatialDomain => y.1) (fst ℝ Space ℝ) (x,θ) :=
    hasFDerivAt_fst
  have hF := ((D.F.smooth t).differentiable (by simp) x).hasFDerivAt.comp (x,θ) hfst
  have hZ := ((coordinate_smooth D G k t).differentiable (by simp) (x,θ)).hasFDerivAt
  have h := (hF.clm_apply hZ).const_smul k⁻¹
  have he : (fun y : SpatialDomain => W (t,y)) =
      fun y => k⁻¹ • D.F.field t y.1 (coordinate D k W (t,y)) := by
    funext y
    simpa only [rawFrame,Data.clamp_coe] using reconstruct D k hk W (t,y)
  have hh : fderiv ℝ (fun y : SpatialDomain =>
      k⁻¹ • D.F.field t y.1 (coordinate D k W (t,y))) (x,θ) =
      k⁻¹ • ((D.F.field t x).comp
        (fderiv ℝ (fun y => coordinate D k W (t,y)) (x,θ)) +
        ((fderiv ℝ (D.F.field t : Space → Space →L[ℝ] Space) x).comp
          (fst ℝ Space ℝ)).flip (coordinate D k W (t,(x,θ)))) := by
    convert! h.fderiv using 1
  rw [he,hh]
  simp only [smul_apply,add_apply,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,rawInverse,Data.clamp_coe,map_smul,map_add,
    D.inverse_left,smul_smul,mul_inv_cancel₀ hk,one_smul]
  abel

end Fields
end EulerPacketCoordinates
