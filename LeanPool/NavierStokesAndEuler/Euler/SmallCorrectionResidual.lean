/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmallCorrectionBounds
public import LeanPool.NavierStokesAndEuler.Euler.ExactLiftedPointwise
public import LeanPool.NavierStokesAndEuler.Euler.PacketTimeAlgebra

@[expose] public section

/-! For a static approximation the prescribed residual is exactly its
spatial convection, at every finite Sobolev order. This verifies the
equation input to the correction theorem rather than assuming it. -/

noncomputable section

namespace EulerSmallCorrection

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLiftedGradientSpace EulerAllOrderCorrectionData EulerAllOrderDriftCorrection
  EulerCylinderSobolevSpace EulerCylinderSobolev EulerCylinderSmoothOrbit
  EulerPacketCylinderField EulerPacketProfileRecursion EulerCylinderPathProduct
  EulerCorrectionResidualCancellation EulerSobolevCoefficientPressure
  EulerConstantCorrection EulerVolterraConvolution EulerMetricTransport
  EulerLiftedWeakDerivative

variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField} (G : Field P T raw)

theorem fieldTower_pointField (t : Icc (0 : ℝ) T) :
    G.toFieldTower.pointField t=pointField P G.path G.orbit t :=
  G.toFieldTower.pointField_unique t _
    (smoothField_continuous P _ (pointField_smooth P G.path G.orbit t))
    (pointField_ae P G.path G.orbit t)

theorem nonlinearity_eq_residual (ε : ℝ) (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    nonlinearity P ((input G ε).atOrder P q) hq t
      ((G.smul ε).toFieldTower.realization (q+1) t) =
      (residual G ε).toFieldTower.realization q t := by
  apply value_injective P
  rw [(residual G ε).toFieldTower_value]
  apply Lp.ext
  have hn := EulerAllOrderDriftCorrection.nonlinearity_value_ae P (input G ε)
    (G.smul ε).toFieldTower q hq t
  have hr := advectionPath_ae P (G.smul ε).path (G.smul ε).path
    (G.smul ε).orbit (G.smul ε).orbit t
  filter_upwards [hn,hr] with x hn hr
  rw [hn]
  change _ = advectionPath P (G.smul ε).path (G.smul ε).path
    (G.smul ε).orbit (G.smul ε).orbit t x
  rw [hr]
  simp only [pointNonlinearity,input,data,tower,coefficient,
    zero_apply,zero_add,smul_zero,Finset.sum_const_zero,add_zero,
    transportDirection,one_smul,inner_zero_left]
  rw [fieldTower_pointField (G.smul ε)]

theorem zero_tower (q : ℕ) (t : Icc (0 : ℝ) T) :
    (Field.zero P T).toFieldTower.realization q t=0 := by
  apply value_injective P
  rw [(Field.zero P T).toFieldTower_value]
  rfl

theorem scaled_zero_tower (ε : ℝ) (q : ℕ) (t : Icc (0 : ℝ) T) :
    ((Field.zero P T).smul ε).toFieldTower.realization q t=0 := by
  apply value_injective P
  rw [((Field.zero P T).smul ε).toFieldTower_value]
  change ε • (0 : LiftL2 P)=0
  exact smul_zero ε

def approximationResidual (hT : 0 < T) (ε : ℝ)
    (hstatic : TimeDerivative hT.le G (Field.zero P T)) :
    ApproximationResidual P hT (input G ε) where
  pressure := (Field.zero P T).toFieldTower
  gradient _ := (gradientSpace P 1 (0 : Space)).zero_mem
  equation q hq t ht := by
    let s : Icc (0 : ℝ) T := ⟨t,ht.1.le,ht.2.le⟩
    have hd := ((G.smul ε).toFieldTower_hasDerivWithinAt ((Field.zero P T).smul ε)
      hT.le (hstatic.smul ε) q s).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    rw [scaled_zero_tower ε q s] at hd
    change HasDerivAt (extendPath T hT.le ((G.smul ε).toFieldTower.realization q))
      ((residual G ε).toFieldTower.realization q s-
        nonlinearity P ((input G ε).atOrder P q) hq s
          ((G.smul ε).toFieldTower.realization (q+1) s)-
        coefficientSobolevOperator P ((input G ε).metric.jet q s)
          ((Field.zero P T).toFieldTower.realization q s)) t
    rw [nonlinearity_eq_residual G ε q hq s,zero_tower,sub_self,map_zero,sub_zero]
    exact hd

end EulerSmallCorrection
