/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCoordinateResidual
public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionSourceData
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionResidualCancellation

/-! The actual coordinate residual identity in every finite Sobolev space.
This discharges the approximation equation, using the source coefficients
and the genuine packet Fields rather than an assumed residual equation. -/

@[expose] public section


noncomputable section

namespace EulerPacketCoordinates

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerPacketPointJets EulerPacketProfileRecursion EulerPacketCylinderField
  EulerPacketCorrectionCoefficients EulerTransversePacketProvider
  EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerCylinderSmoothOrbit EulerLpCylinderRectangular EulerSobolevCoefficientPressure
  EulerSobolevTransport EulerCorrectionOperators EulerCorrectionResidualCancellation
  EulerVolterraConvolution EulerMetricTransport EulerLiftedWeakDerivative EulerLpCylinderTranslation
open scoped ContDiff

/-- Cache the standard `NormedAddCommGroup Space` instance to shorten typeclass synthesis. -/
local instance instPacketCoordinateSobolev1 : NormedAddCommGroup Space := inferInstance
/-- Cache the standard `NormedSpace ℝ Space` instance to shorten typeclass synthesis. -/
local instance instPacketCoordinateSobolev2 : NormedSpace ℝ Space := inferInstance

variable {P : ℝ} [Fact (0 < P)]

private theorem coefficient_value_ae {T : ℝ} {a : Domain → Space →L[ℝ] Space}
    (A : MatrixCoefficient T a) (q : ℕ) (t : Icc (0 : ℝ) T)
    (u : SobolevSpace P q) (f : LiftDomain P → Space)
    (hu : (value P u : LiftDomain P → Space) =ᵐ[liftMeasure P] f) :
    (value P (coefficientSobolevOperator P ((A.toCoefficientTower P).jet q t) u) :
      LiftDomain P → Space) =ᵐ[liftMeasure P] fun x => A.path t x.1 (f x) := by
  rw [MatrixCoefficient.toCoefficientTower_sobolev_value P A q t u]
  filter_upwards [EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (A.path t))
    (value P u),hu] with x hA hf
  exact hA.trans (congrArg (A.path t x.1) hf)

private theorem transport_value_ae {T : ℝ} {z : VectorField}
    (Z : Field P T z) (κ : ℝ) (m : Space) (hκ : |κ| ≤ 1) (hm : ‖m‖ ≤ 1)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    (value P (transportBilinear P hq (velocityComponents κ m)
      (velocityComponents_norm κ m hκ hm)
      (Z.toFieldTower.realization (q+1) t) (Z.toFieldTower.realization (q+1) t)) :
        LiftDomain P → Space) =ᵐ[liftMeasure P] fun x =>
      fieldFDeriv P (pointField P Z.path Z.orbit t) x
        (transportDirection κ m (pointField P Z.path Z.orbit t x)) := by
  have h := transportBilinear_ae P hq (velocityComponents κ m)
    (velocityComponents_norm κ m hκ hm) _ _ _ _
    (Z.toFieldTower_value_ae (q+1) t) (Z.toFieldTower_value_ae (q+1) t)
    (pointField_smooth P Z.path Z.orbit t)
  filter_upwards [h] with x hx
  rw [hx,← velocityComponents_direction κ m]
  change (∑ i : Fin 4, velocityComponents κ m i (pointField P Z.path Z.orbit t x) •
      fieldFDeriv P (pointField P Z.path Z.orbit t) x (standardDirection i)) = _
  rw [map_sum]
  simp only [map_smul]

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : Data U)

/-- Normalized residual, given by `k • rawInverse D z (slicedMomentumResidual (Icc (0 : ℝ) D.T)
k⁻¹ (rawInverse D z) (D.strain z) (D.normalField z) W p z)`. -/
def normalizedResidual (k : ℝ) (W : VectorField) (p : ScalarField) (z : Domain) : Space :=
  k • rawInverse D z (slicedMomentumResidual (Icc (0 : ℝ) D.T) k⁻¹
    (rawInverse D z) (D.strain z) (D.normalField z) W p z)

private theorem nonlinearity_value_ae (κ : ℝ) (hκ : |κ| ≤ 1)
    {z r : VectorField} (Z : Field P D.T z) (R : Field P D.T r)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) D.T) :
    (value P (nonlinearity P ((correctionDataOfFields D P κ hκ Z R).atOrder P q) hq t
      (Z.toFieldTower.realization (q+1) t)) : LiftDomain P → Space) =ᵐ[liftMeasure P]
      fun x => (linearCoefficient D).path t x.1 (pointField P Z.path Z.orbit t x) +
        fieldFDeriv P (pointField P Z.path Z.orbit t) x
          (transportDirection κ D.m₀ (pointField P Z.path Z.orbit t x)) +
        ∑ i : Fin 3, (pointField P Z.path Z.orbit t x) i •
          (quadraticCoefficient D κ i).path t x.1 (pointField P Z.path Z.orbit t x) := by
  let u := Z.toFieldTower.realization (q+1) t
  let a := coefficientSobolevOperator P ((linearTower D P).jet q t) (truncateOperator P q u)
  let b := transportBilinear P hq (velocityComponents κ D.m₀)
    (velocityComponents_norm κ D.m₀ hκ D.m₀_unit.le) u u
  let c := algebraicBilinear P hq
    (fun i => coefficientSobolevOperator P ((quadraticTower D P κ i).jet q t)) u u
  have ha := coefficient_value_ae (linearCoefficient D) q t (truncateOperator P q u)
    (pointField P Z.path Z.orbit t) (by
      simpa only [value_truncateOperator] using Z.toFieldTower_value_ae (q+1) t)
  have hb := transport_value_ae Z κ D.m₀ hκ D.m₀_unit.le q hq t
  have hc := algebraicBilinear_ae P hq (fun i => (quadraticTower D P κ i).coefficient t)
    (fun i => (quadraticTower D P κ i).jet q t) u u _ _
    (Z.toFieldTower_value_ae (q+1) t) (Z.toFieldTower_value_ae (q+1) t)
  change ((valueOperator P q) (a+(b+c)) : LiftDomain P → Space) =ᵐ[liftMeasure P] _
  rw [map_add,map_add]
  filter_upwards [Lp.coeFn_add (value P a) (value P b+value P c),
    Lp.coeFn_add (value P b) (value P c),ha,hb,hc] with x hx hy ha hb hc
  change (value P a + (value P b + value P c)) x = _
  simp only [Pi.add_apply] at hx hy
  change (value P a) x = _ at ha
  change (value P b) x = _ at hb
  change (value P c) x = _ at hc
  rw [hx,hy,ha,hb,hc]
  simp only [add_assoc,quadraticTower,MatrixCoefficient.toCoefficientTower_coefficient]

section Equation

variable (k : ℝ) (hk : k ≠ 0) (hκ : |k⁻¹| ≤ 1)
  {W Wt : VectorField} (G : Field P D.T W) (Gt : Field P D.T Wt)
  (hW : TimeDerivative D.T_pos.le G Gt) (p : ScalarField)
  (R : Field P D.T (normalizedResidual D k W p))
  (Pa : Field P D.T (coordinatePressure D k p))

/-- The data used for cancellation has the literal normalized packet field
and residual. Its coefficients are the original deformation coefficients. -/
def coordinateData : EulerAllOrderCorrectionData.Data P D.T :=
  correctionDataOfFields D P k⁻¹ hκ (coordinateField D G k) R

include hk hW in
theorem sobolev_residual_identity (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) D.T) :
    R.toFieldTower.realization q t =
      (coordinateTimeField D G Gt k).toFieldTower.realization q t +
        nonlinearity P ((coordinateData D k hκ G p R).atOrder P q) hq t
          ((coordinateField D G k).toFieldTower.realization (q+1) t) +
        coefficientSobolevOperator P ((metricTower D P).jet q t)
          (Pa.toFieldTower.realization q t) := by
  let Z := coordinateField D G k
  let Zt := coordinateTimeField D G Gt k
  let A := coordinateData D k hκ G p R
  let N := nonlinearity P (A.atOrder P q) hq t (Z.toFieldTower.realization (q+1) t)
  let Q := coefficientSobolevOperator P ((metricTower D P).jet q t)
    (Pa.toFieldTower.realization q t)
  have hn := nonlinearity_value_ae D k⁻¹ hκ Z R q hq t
  have hp := coefficient_value_ae (metricCoefficient D) q t
    (Pa.toFieldTower.realization q t) (pointField P Pa.path Pa.orbit t)
    (Pa.toFieldTower_value_ae q t)
  apply value_injective P
  change value P (R.toFieldTower.realization q t) =
    (valueOperator P q) (Zt.toFieldTower.realization q t+N+Q)
  rw [map_add,map_add]
  apply Lp.ext
  filter_upwards [R.toFieldTower_value_ae q t,Zt.toFieldTower_value_ae q t,hn,hp,
    Lp.coeFn_add (value P (Zt.toFieldTower.realization q t)) (value P N),
    Lp.coeFn_add (value P (Zt.toFieldTower.realization q t)+value P N) (value P Q)]
    with x hr ht hn hp hs hs'
  change (value P (R.toFieldTower.realization q t)) x =
    (value P (Zt.toFieldTower.realization q t)+value P N+value P Q) x
  simp only [Pi.add_apply] at hs hs'
  change (value P N) x = _ at hn
  change (value P Q) x = _ at hp
  rw [hr,hs',hs,ht,hn,hp]
  obtain ⟨θ,hθ⟩ := QuotientAddGroup.mk_surjective x.2
  have he := normalized_residual D G Gt k hk hW p t x.1 θ
  change normalizedResidual D k W p (t,(x.1,θ)) = _ at he
  rw [R.raw_eq t x.1 θ,Zt.raw_eq t x.1 θ] at he
  simp only [transport,algebraic] at he
  rw [Z.raw_fderiv t x.1 θ,(linearCoefficient D).raw_eq t x.1 θ,
    (metricCoefficient D).raw_eq t x.1 θ,Pa.raw_eq t x.1 θ] at he
  simp only [Z.raw_eq t x.1 θ] at he
  have hquad (i : Fin 3) : rawQuadratic D k⁻¹ i (t,(x.1,θ)) =
      (quadraticCoefficient D k⁻¹ i).path t x.1 :=
    (quadraticCoefficient D k⁻¹ i).raw_eq t x.1 θ
  simp only [hquad,hθ] at he
  simpa only [transportDirection,add_assoc] using he

include hk hW in
/-- The approximation's actual all-order derivative is its literal
residual minus the full nonlinearity and its own actual pressure. -/
theorem approximation_hasDerivWithinAt (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt
      (extendPath D.T D.T_pos.le ((coordinateData D k hκ G p R).approximation.realization q))
      ((coordinateData D k hκ G p R).residual.realization q t -
        nonlinearity P ((coordinateData D k hκ G p R).atOrder P q) hq t
          ((coordinateData D k hκ G p R).approximation.realization (q+1) t) -
        coefficientSobolevOperator P ((coordinateData D k hκ G p R).metric.jet q t)
          (Pa.toFieldTower.realization q t)) (Icc (0 : ℝ) D.T) t := by
  have hd := (coordinateField D G k).toFieldTower_hasDerivWithinAt
    (coordinateTimeField D G Gt k) D.T_pos.le (coordinateField_time D G Gt k hW) q t
  apply hd.congr_deriv
  change (coordinateTimeField D G Gt k).toFieldTower.realization q t =
    R.toFieldTower.realization q t -
      nonlinearity P ((coordinateData D k hκ G p R).atOrder P q) hq t
        ((coordinateField D G k).toFieldTower.realization (q+1) t) -
      coefficientSobolevOperator P ((metricTower D P).jet q t) (Pa.toFieldTower.realization q t)
  rw [sobolev_residual_identity D k hk hκ G Gt hW p R Pa q hq t]
  abel

include hk hW in
theorem approximation_hasDerivAt (q : ℕ) (hq : 6 ≤ q) (t : ℝ) (ht : t ∈ Ioo 0 D.T) :
    HasDerivAt
      (extendPath D.T D.T_pos.le ((coordinateData D k hκ G p R).approximation.realization q))
      ((coordinateData D k hκ G p R).residual.realization q ⟨t,ht.1.le,ht.2.le⟩ -
        nonlinearity P ((coordinateData D k hκ G p R).atOrder P q) hq ⟨t,ht.1.le,ht.2.le⟩
          ((coordinateData D k hκ G p R).approximation.realization (q+1) ⟨t,ht.1.le,ht.2.le⟩) -
        coefficientSobolevOperator P ((coordinateData D k hκ G p R).metric.jet q
            ⟨t,ht.1.le,ht.2.le⟩)
          (Pa.toFieldTower.realization q ⟨t,ht.1.le,ht.2.le⟩)) t :=
  (approximation_hasDerivWithinAt D k hk hκ G Gt hW p R Pa q hq
    ⟨t,ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

end Equation

end EulerPacketCoordinates
