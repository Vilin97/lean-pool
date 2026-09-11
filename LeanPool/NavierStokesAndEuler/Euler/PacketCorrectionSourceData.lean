/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldTower
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceCorrectionCoefficients

/-! Actual all-order correction data from the source deformation and two
prescribed packet fields. No correction solution or energy budget is assumed. -/

section

/-! Positivity and the literal inverse identity for the pressure metric.
Both follow from the prescribed deformation and its two-sided inverse. -/

@[expose] public section

noncomputable section

namespace EulerPacketCorrectionCoefficients

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace

theorem norm_sq_lower_of_inverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : E →L[ℝ] E) (b : ℝ) (hb : 0 < b)
    (hBA : ∀ v, B (A v) = v) (hB : ‖B‖ ≤ b) (v : E) :
    b⁻¹^2*‖v‖^2 ≤ ‖A v‖^2 := by
  have hn : ‖v‖ ≤ b*‖A v‖ := by
    calc
      ‖v‖ = ‖B (A v)‖ := by rw [hBA]
      _ ≤ ‖B‖*‖A v‖ := B.le_opNorm _
      _ ≤ b*‖A v‖ := mul_le_mul_of_nonneg_right hB (norm_nonneg _)
  have hd : b⁻¹*‖v‖ ≤ ‖A v‖ := by
    rw [← div_eq_inv_mul]
    exact (div_le_iff₀ hb).2 (by simpa only [mul_comm] using hn)
  have hs := (sq_le_sq₀ (mul_nonneg (inv_nonneg.mpr hb.le) (norm_nonneg _))
    (norm_nonneg (A v))).2 hd
  simpa only [mul_pow] using hs

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U)

theorem frame_adjoint_inverse (t : Icc (0 : ℝ) D.T) (x v : Space) :
    (D.F.field t x).adjoint ((D.FInv.field t x).adjoint v) = v := by
  apply ext_inner_right ℝ
  intro w
  rw [adjoint_inner_left,adjoint_inner_left,D.inverse_left]

theorem inverse_adjoint_frame (t : Icc (0 : ℝ) D.T) (x v : Space) :
    (D.FInv.field t x).adjoint ((D.F.field t x).adjoint v) = v := by
  apply ext_inner_right ℝ
  intro w
  rw [adjoint_inner_left,adjoint_inner_left,D.inverse_right]

theorem metric_inner (t : Icc (0 : ℝ) D.T) (x v w : Space) :
    ⟪(metricCoefficient D).path t x v,w⟫_ℝ =
      ⟪(D.FInv.field t x).adjoint v,(D.FInv.field t x).adjoint w⟫_ℝ := by
  change ⟪D.FInv.field t x ((D.FInv.field t x).adjoint v),w⟫_ℝ = _
  rw [← adjoint_inner_right]

theorem inverseMetric_inner (t : Icc (0 : ℝ) D.T) (x v w : Space) :
    ⟪(inverseMetricCoefficient D).path t x v,w⟫_ℝ =
      ⟪D.F.field t x v,D.F.field t x w⟫_ℝ := by
  change ⟪(D.F.field t x).adjoint (D.F.field t x v),w⟫_ℝ = _
  rw [adjoint_inner_left]

theorem metric_coercive (t : Icc (0 : ℝ) D.T) (x v : Space) :
    D.normalLower*‖v‖^2 ≤ ⟪(metricCoefficient D).path t x v,v⟫_ℝ := by
  rw [metric_inner,real_inner_self_eq_norm_sq]
  exact norm_sq_lower_of_inverse (D.FInv.field t x).adjoint (D.F.field t x).adjoint
    D.frameBound D.frameBound_pos (frame_adjoint_inverse D t x)
    (by simpa only [ContinuousLinearMap.adjoint.norm_map] using D.frame_norm t x) v

theorem inverseMetric_coercive (t : Icc (0 : ℝ) D.T) (x v : Space) :
    D.frameLower*‖v‖^2 ≤ ⟪(inverseMetricCoefficient D).path t x v,v⟫_ℝ := by
  rw [inverseMetric_inner,real_inner_self_eq_norm_sq]
  exact norm_sq_lower_of_inverse (D.F.field t x) (D.FInv.field t x)
    D.inverseBound D.inverseBound_pos (D.inverse_left t x) (D.inverse_norm t x) v

theorem inverseMetric_inverse (t : Icc (0 : ℝ) D.T) (x v : Space) :
    (inverseMetricCoefficient D).path t x ((metricCoefficient D).path t x v) = v := by
  change (D.F.field t x).adjoint
    (D.F.field t x (D.FInv.field t x ((D.FInv.field t x).adjoint v))) = v
  rw [D.inverse_right,frame_adjoint_inverse]

theorem metric_inverseMetric (t : Icc (0 : ℝ) D.T) (x v : Space) :
    (metricCoefficient D).path t x ((inverseMetricCoefficient D).path t x v) = v := by
  change D.FInv.field t x
    ((D.FInv.field t x).adjoint ((D.F.field t x).adjoint (D.F.field t x v))) = v
  rw [inverse_adjoint_frame,D.inverse_left]

theorem metric_symmetric (t : Icc (0 : ℝ) D.T) (x v w : Space) :
    ⟪(metricCoefficient D).path t x v,w⟫_ℝ =
      ⟪v,(metricCoefficient D).path t x w⟫_ℝ := by
  calc
    _ = ⟪(D.FInv.field t x).adjoint v,(D.FInv.field t x).adjoint w⟫_ℝ :=
      metric_inner D t x v w
    _ = ⟪(D.FInv.field t x).adjoint w,(D.FInv.field t x).adjoint v⟫_ℝ :=
      real_inner_comm _ _
    _ = ⟪(metricCoefficient D).path t x w,v⟫_ℝ := (metric_inner D t x w v).symm
    _ = _ := real_inner_comm _ _

theorem inverseMetric_symmetric (t : Icc (0 : ℝ) D.T) (x v w : Space) :
    ⟪(inverseMetricCoefficient D).path t x v,w⟫_ℝ =
      ⟪v,(inverseMetricCoefficient D).path t x w⟫_ℝ := by
  calc
    _ = ⟪D.F.field t x v,D.F.field t x w⟫_ℝ := inverseMetric_inner D t x v w
    _ = ⟪D.F.field t x w,D.F.field t x v⟫_ℝ := real_inner_comm _ _
    _ = ⟪(inverseMetricCoefficient D).path t x w,v⟫_ℝ :=
      (inverseMetric_inner D t x w v).symm
    _ = _ := real_inner_comm _ _

variable (P : ℝ) [Fact (0 < P)]

theorem metricTower_coercive (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) (v : Space) :
    D.normalLower*‖v‖^2 ≤ ⟪((metricTower D P).coefficient t).coefficient x v,v⟫_ℝ :=
  metric_coercive D t x.1 v

theorem inverseMetricTower_inverse (t : Icc (0 : ℝ) D.T)
    (x : LiftDomain P) (v : Space) :
    ((inverseMetricTower D P).coefficient t).coefficient x
      (((metricTower D P).coefficient t).coefficient x v) = v :=
  inverseMetric_inverse D t x.1 v

end EulerPacketCorrectionCoefficients

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketCorrectionCoefficients

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketCylinderField
  EulerAllOrderCorrectionData EulerLiftedGradientSpace EulerPacketProfileRecursion

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) (P : ℝ) [Fact (0 < P)]

/-- Correction data, bundling `κ`, `direction`, `scale_bound`, `direction_bound` and the
required compatibility proofs. -/
def correctionData (κ : ℝ) (hκ : |κ| ≤ 1)
    (approximation residual : FieldTower P D.T) : Data P D.T where
  κ := κ
  direction := D.m₀
  scale_bound := hκ
  direction_bound := D.m₀_unit.le
  metric := metricTower D P
  metric_continuous := metricTower_continuous D P
  coercivity := D.normalLower
  coercivity_pos := D.normalLower_pos
  metric_pos := metricTower_coercive D P
  linear := linearTower D P
  quadratic := quadraticTower D P κ
  approximation := approximation
  residual := residual

/-- Correction data of fields, given by `correctionData D P κ hκ Z.toFieldTower G.toFieldTower`. -/
def correctionDataOfFields (κ : ℝ) (hκ : |κ| ≤ 1)
    {z r : VectorField} (Z : Field P D.T z) (G : Field P D.T r) : Data P D.T :=
  correctionData D P κ hκ Z.toFieldTower G.toFieldTower

@[simp] theorem correctionDataOfFields_approximation (κ : ℝ) (hκ : |κ| ≤ 1)
    {z r : VectorField} (Z : Field P D.T z) (G : Field P D.T r) :
    (correctionDataOfFields D P κ hκ Z G).approximation.field = Z.path := rfl

@[simp] theorem correctionDataOfFields_residual (κ : ℝ) (hκ : |κ| ≤ 1)
    {z r : VectorField} (Z : Field P D.T z) (G : Field P D.T r) :
    (correctionDataOfFields D P κ hκ Z G).residual.field = G.path := rfl

@[simp] theorem correctionData_metric (κ : ℝ) (hκ : |κ| ≤ 1)
    (Z G : FieldTower P D.T) (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    (((correctionData D P κ hκ Z G).metric).coefficient t).coefficient x =
      (D.FInv.field t x.1).comp (D.FInv.field t x.1).adjoint := rfl

@[simp] theorem correctionData_linear (κ : ℝ) (hκ : |κ| ≤ 1)
    (Z G : FieldTower P D.T) (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    (((correctionData D P κ hκ Z G).linear).coefficient t).coefficient x =
      (2 : ℝ) • (D.FInv.field t x.1).comp (D.F₁.field t x.1) := rfl

theorem correctionData_quadratic (κ : ℝ) (hκ : |κ| ≤ 1)
    (Z G : FieldTower P D.T) (i : Fin 3) (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    (((correctionData D P κ hκ Z G).quadratic i).coefficient t).coefficient x =
      κ • (D.FInv.field t x.1).comp
        (fderiv ℝ (D.F.field t : Space → Space →L[ℝ] Space) x.1
          (EuclideanSpace.single i 1)) :=
  quadraticTower_apply D P κ i t x

end EulerPacketCorrectionCoefficients
