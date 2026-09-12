/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderJetOperations
public import LeanPool.NavierStokesAndEuler.Euler.PacketSlicedResidual
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderPressureLocality
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceCorrectionCoefficients
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketTimeData
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderFullTime

/-! Exact coordinate normalization of the actual packet residual.  The
linear, metric, and derivative-free quadratic coefficients are precisely
those constructed in `PacketSourceCorrectionCoefficients`. -/

section

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

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketCoordinates

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerPacketPointJets EulerPacketProfileRecursion EulerPacketCylinderField
  EulerPacketCorrectionCoefficients EulerTransversePacketProvider
  EulerCylinderPathProduct
open scoped ContDiff

/-- Cache the standard `NormedAddCommGroup Space` instance to shorten typeclass synthesis. -/
local instance instPacketCoordinateResidual1 : NormedAddCommGroup Space := inferInstance
/-- Cache the standard `NormedSpace ℝ Space` instance to shorten typeclass synthesis. -/
local instance instPacketCoordinateResidual2 : NormedSpace ℝ Space := inferInstance

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : Data U)

/-- Transport, given by `fderiv ℝ (fun y => Z (z.1,y)) z.2 (κ • Z z,⟪D.m₀,Z z⟫_ℝ)`. -/
def transport (κ : ℝ) (Z : VectorField) (z : Domain) : Space :=
  fderiv ℝ (fun y => Z (z.1,y)) z.2 (κ • Z z,⟪D.m₀,Z z⟫_ℝ)

/-- Algebraic, given by `∑ i : Fin 3, (Z z) i • rawQuadratic D κ i z (Z z)`. -/
def algebraic (κ : ℝ) (Z : VectorField) (z : Domain) : Space :=
  ∑ i : Fin 3, (Z z) i • rawQuadratic D κ i z (Z z)

/-- Coordinate pressure, given by `k • pressureGradient p z + k^2 • ((pressureJet p z).2
angleDirection • D.m₀)`. -/
def coordinatePressure (k : ℝ) (p : ScalarField) (z : Domain) : Space :=
  k • pressureGradient p z + k^2 • ((pressureJet p z).2 angleDirection • D.m₀)

/-- Lifted pressure, given by `κ • pressureGradient p z + (pressureJet p z).2 angleDirection •
D.m₀`. -/
def liftedPressure (κ : ℝ) (p : ScalarField) (z : Domain) : Space :=
  κ • pressureGradient p z + (pressureJet p z).2 angleDirection • D.m₀

theorem transport_formula (κ : ℝ) (Z : VectorField) (z : Domain) :
    transport D κ Z z =
      κ • fderiv ℝ (fun y => Z (z.1,y)) z.2 (Z z,0) +
      ⟪D.m₀,Z z⟫_ℝ • fderiv ℝ (fun y => Z (z.1,y)) z.2 (0,1) := by
  have he : (κ • Z z,⟪D.m₀,Z z⟫_ℝ) =
      κ • (Z z,(0 : ℝ)) + ⟪D.m₀,Z z⟫_ℝ • ((0 : Space),(1 : ℝ)) := by
    simp only [Prod.smul_mk,Prod.mk_add_mk,smul_zero,add_zero,smul_eq_mul,mul_one,mul_zero,zero_add]
  rw [transport,he,map_add,map_smul,map_smul]

theorem algebraic_formula (κ : ℝ) (Z : VectorField) (z : Domain) :
    algebraic D κ Z z =
      κ • rawInverse D z
        (fderiv ℝ (fun x => rawFrame D (z.1,(x,z.2.2))) z.2.1 (Z z) (Z z)) := by
  let A := fderiv ℝ (fun x => rawFrame D (z.1,(x,z.2.2))) z.2.1
  have hv : (∑ i : Fin 3, (Z z) i • EuclideanSpace.single i 1) = Z z :=
    sum_components (Z z)
  calc
    _ = ∑ i : Fin 3, κ • rawInverse D z (A ((Z z) i • EuclideanSpace.single i 1) (Z z)) := by
      apply Finset.sum_congr rfl
      intro i _
      change (Z z) i • (κ • rawInverse D z (A (EuclideanSpace.single i 1) (Z z))) = _
      simp only [map_smul,smul_apply]
      exact smul_comm _ _ _
    _ = κ • rawInverse D z (A (∑ i : Fin 3, (Z z) i • EuclideanSpace.single i 1) (Z z)) := by
      simp only [map_sum,sum_apply,Finset.smul_sum]
    _ = _ := by rw [hv]

theorem normalized_pressure (k : ℝ) (p : ScalarField) (z : Domain) :
    k • rawInverse D z
      (slowPressure (rawInverse D z) (pressureJet p z) +
        k • fastPressure (D.normalField z) (pressureJet p z)) =
      rawMetric D z (coordinatePressure D k p z) := by
  change k • rawInverse D z
      ((rawInverse D z).adjoint (pressureGradient p z) +
        k • ((pressureJet p z).2 angleDirection • (rawInverse D z).adjoint D.m₀)) =
    rawInverse D z ((rawInverse D z).adjoint
      (k • pressureGradient p z + k^2 • ((pressureJet p z).2 angleDirection • D.m₀)))
  simp only [map_add,map_smul,smul_add,smul_smul,pow_two]
  module

theorem coordinatePressure_eq_lifted (k : ℝ) (hk : k ≠ 0) (p : ScalarField)
    (z : Domain) (hp : DifferentiableAt ℝ (fun y => p (z.1, y)) z.2) :
    coordinatePressure D k p z = liftedPressure D k⁻¹ (k^2 • p) z := by
  have hd : fderiv ℝ (fun y => (k^2 • p) (z.1,y)) z.2 =
      k^2 • fderiv ℝ (fun y => p (z.1,y)) z.2 := by
    convert! (hp.hasFDerivAt.const_smul (k^2)).fderiv using 1
  unfold liftedPressure coordinatePressure
  rw [pressureGradient_eq_spatialDual,pressureGradient_eq_spatialDual,
    pressureJet_angle,pressureJet_angle,hd]
  simp only [smul_comp,map_smul,smul_apply,smul_smul]
  have he : k⁻¹*k^2 = k := by field_simp
  rw [he]
  simp only [smul_eq_mul]

section Fields

variable {P : ℝ} [Fact (0 < P)] {W Wt : VectorField}
  (G : Field P D.T W) (Gt : Field P D.T Wt)

theorem normalized_linear (k : ℝ) (hW : TimeDerivative D.T_pos.le G Gt)
    (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    k • rawInverse D (t,(x,θ))
      (linearPart (D.strain (t,(x,θ))) (slicedJet (Icc (0 : ℝ) D.T) W (t,(x,θ)))) =
      coordinateTime D k W Wt (t,(x,θ)) +
        rawLinear D (t,(x,θ)) (coordinate D k W (t,(x,θ))) := by
  have hf : D.F₁.field t x (D.FInv.field t x (W (t,(x,θ)))) =
      D.M.field t x (W (t,(x,θ))) := by
    rw [D.strain_equation,D.inverse_right]
  change k • rawInverse D (t,(x,θ))
      ((slicedJet (Icc (0 : ℝ) D.T) W (t,(x,θ))).2 timeDirection +
        D.strain (t,(x,θ)) (W (t,(x,θ)))) = _
  rw [G.slicedJet_temporal D.T_pos Gt hW,coordinateTime_formula]
  simp only [rawInverse,rawLinear,rawFrameTime,coordinate,Data.strain,Data.clamp_coe,
    smul_apply,comp_apply,map_smul,hf,map_add,smul_add,smul_smul,smul_sub]
  module

include G in
theorem normalized_nonlinear (k : ℝ) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    k • rawInverse D (t,(x,θ))
      (slowAdvection (rawInverse D (t,(x,θ)))
          (slicedJet (Icc (0 : ℝ) D.T) W (t,(x,θ)))
          (slicedJet (Icc (0 : ℝ) D.T) W (t,(x,θ))) +
        k • fastAdvection (D.normalField (t,(x,θ)))
          (slicedJet (Icc (0 : ℝ) D.T) W (t,(x,θ)))
          (slicedJet (Icc (0 : ℝ) D.T) W (t,(x,θ)))) =
      transport D k⁻¹ (coordinate D k W) (t,(x,θ)) +
        algebraic D k⁻¹ (coordinate D k W) (t,(x,θ)) := by
  let z : Domain := (t,(x,θ))
  let Z := coordinate D k W
  have hi : rawInverse D z (W z) = k⁻¹ • Z z := by
    dsimp [Z,coordinate]
    rw [smul_smul,inv_mul_cancel₀ hk,one_smul]
  have hs := normalized_spatial_derivative D G k hk t x θ (rawInverse D z (W z),0)
  have ha := normalized_spatial_derivative D G k hk t x θ (0,1)
  change k • rawInverse D z (fderiv ℝ (fun y => W (t,y)) (x,θ)
      (rawInverse D z (W z),0)) =
    rawInverse D z (fderiv ℝ (D.F.field t : Space → Space →L[ℝ] Space) x
      (rawInverse D z (W z)) (Z z)) + fderiv ℝ (fun y => Z (t,y)) (x,θ)
      (rawInverse D z (W z),0) at hs
  have he : (k⁻¹ • Z z,(0 : ℝ)) = k⁻¹ • (Z z,(0 : ℝ)) := by simp
  have hslow : k • rawInverse D z (fderiv ℝ (fun y => W (t,y)) (x,θ)
      (rawInverse D z (W z),0)) =
      k⁻¹ • rawInverse D z (fderiv ℝ (D.F.field t : Space → Space →L[ℝ] Space) x
        (Z z) (Z z)) + k⁻¹ • fderiv ℝ (fun y => Z (t,y)) (x,θ) (Z z,0) :=
    hs.trans (by simp only [hi,he,map_smul,smul_apply])
  simp only [map_zero,zero_apply,map_zero,zero_add] at ha
  have hfast : k • rawInverse D z
      (k • (⟪D.normalField z,W z⟫_ℝ • fderiv ℝ (fun y => W (t,y)) (x,θ) (0,1))) =
      ⟪D.m₀,Z z⟫_ℝ • fderiv ℝ (fun y => Z (t,y)) (x,θ) (0,1) := by
    calc
      _ = (k*⟪D.normalField z,W z⟫_ℝ) •
          (k • rawInverse D z (fderiv ℝ (fun y => W (t,y)) (x,θ) (0,1))) := by
        simp only [map_smul,smul_smul]
        congr 1
        ring
      _ = _ := by rw [← normal_coordinate D k W z,ha]
  change k • rawInverse D z
      ((slicedJet (Icc (0 : ℝ) D.T) W z).2 (spatialInjection (rawInverse D z (W z))) +
        k • (⟪D.normalField z,W z⟫_ℝ •
          (slicedJet (Icc (0 : ℝ) D.T) W z).2 angleDirection)) = _
  rw [slicedJet_space,slicedJet_angle,map_add,smul_add,hslow,hfast,
    transport_formula,algebraic_formula]
  simp only [rawFrame,Data.clamp_coe]
  abel

theorem normalized_residual (k : ℝ) (hk : k ≠ 0) (hW : TimeDerivative D.T_pos.le G Gt)
    (p : ScalarField) (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    k • rawInverse D (t,(x,θ))
      (slicedMomentumResidual (Icc (0 : ℝ) D.T) k⁻¹
        (rawInverse D (t,(x,θ))) (D.strain (t,(x,θ))) (D.normalField (t,(x,θ)))
        W p (t,(x,θ))) =
      coordinateTime D k W Wt (t,(x,θ)) +
        rawLinear D (t,(x,θ)) (coordinate D k W (t,(x,θ))) +
        transport D k⁻¹ (coordinate D k W) (t,(x,θ)) +
        algebraic D k⁻¹ (coordinate D k W) (t,(x,θ)) +
        rawMetric D (t,(x,θ)) (coordinatePressure D k p (t,(x,θ))) := by
  have hl := normalized_linear D G Gt k hW t x θ
  have hn := normalized_nonlinear D G k hk t x θ
  have hp := normalized_pressure D k p (t,(x,θ))
  simp only [map_add,smul_add] at hl hn hp
  simp only [slicedMomentumResidual,inv_inv,map_add,smul_add]
  rw [hl]
  linear_combination (norm := module) hn + hp

end Fields
end EulerPacketCoordinates
