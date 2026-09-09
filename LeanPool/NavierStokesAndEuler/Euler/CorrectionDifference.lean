/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevL2Stability
public import LeanPool.NavierStokesAndEuler.Euler.GevreyCorrectionSplit

@[expose] public section

/-! Exact nonlinear correction differences and their genuine L² lower-order bounds. -/

noncomputable section

namespace EulerCorrectionDifference

open MeasureTheory EulerLiftedGradientSpace EulerSpatialSobolevInverse EulerCylinderSobolev
  EulerCylinderSobolevSpace EulerSobolevL2Product EulerSobolevTransport EulerCorrectionOperators
  EulerSobolevCoefficientPressure EulerSobolevL2Stability
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual lower-order part of the difference of two correction equations. -/
def differenceRemainder {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (t : T)
    (u v : SobolevSpace period (q+1)) : SobolevSpace period q :=
  transportBilinear period hq (velocityComponents D.κ D.direction)
    (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound) (u-v)
      (D.approximation t+v) +
    coefficientSobolevOperator period (D.linear.jet t) (truncateOperator period q (u-v)) +
    algebraicBilinear period hq (fun i => coefficientSobolevOperator period ((D.quadratic i).jet t))
      (D.approximation t+u) (u-v) +
    algebraicBilinear period hq (fun i => coefficientSobolevOperator period ((D.quadratic i).jet t))
      (u-v) (D.approximation t+v)

/-- Exact bilinear subtraction exposes one cancellable top transport and the actual lower-order difference. -/
theorem rawSource_sub {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (t : T)
    (u v : SobolevSpace period (q+1)) :
    D.rawSource period hq t u-D.rawSource period hq t v =
      transportBilinear period hq (velocityComponents D.κ D.direction)
        (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound) (D.approximation
          t+u) (u-v)+
      differenceRemainder period D hq t u v := by
  let B := eulerBilinear period hq (velocityComponents D.κ D.direction)
    (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound)
    (fun i => coefficientSobolevOperator period ((D.quadratic i).jet t))
  let A := (coefficientSobolevOperator period (D.linear.jet t)).comp (truncateOperator period q)
  change (D.residual t+linearize B A (D.approximation t) u+B u u)-
    (D.residual t+linearize B A (D.approximation t) v+B v v)=_
  dsimp only [B,A]
  simp only [differenceRemainder,linearize_apply,eulerBilinear,add_apply,map_add,map_sub,sub_apply,
    ContinuousLinearMap.comp_apply]
  abel

/-- The actual algebraic quadratic term has an L² bound in its second input. -/
theorem algebraic_norm {q : ℕ} (hq : 6 ≤ q) (C : Fin 3 → SmoothCoefficient period)
    (K : ∀ i, CoefficientJet period standardDirection q (C i))
    (u v : SobolevSpace period (q+1)) :
    ‖value period (algebraicBilinear period hq (fun i => coefficientSobolevOperator period (K i)) u
      v)‖ ≤
      ((∑ i : Fin 3, ((C i).bound : ℝ))*sobolevEmbeddingConstant period q)*‖u‖*‖value period v‖ :=
        by
  rw [algebraicBilinear_apply]
  change ‖(valueOperator period q) (∑ i : Fin 3, _)‖ ≤ _
  rw [map_sum]
  change ‖∑ i : Fin 3, value period (coefficientSobolevOperator period (K i) (coordinateProduct
    period hq i u v))‖ ≤ _
  have h := (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin
    3))) =>
    coordinate_coefficient_norm period hq (C i) (K i) i u v))
  simpa only [Finset.sum_mul] using h

/-- The same actual algebraic quadratic term has an L² bound in its first input. -/
theorem algebraic_reverse_norm {q : ℕ} (hq : 6 ≤ q) (C : Fin 3 → SmoothCoefficient period)
    (K : ∀ i, CoefficientJet period standardDirection q (C i))
    (u v : SobolevSpace period (q+1)) :
    ‖value period (algebraicBilinear period hq (fun i => coefficientSobolevOperator period (K i)) u
      v)‖ ≤
      ((∑ i : Fin 3, ((C i).bound : ℝ))*sobolevEmbeddingConstant period q)*‖v‖*‖value period u‖ :=
        by
  rw [algebraicBilinear_apply]
  change ‖(valueOperator period q) (∑ i : Fin 3, _)‖ ≤ _
  rw [map_sum]
  change ‖∑ i : Fin 3, value period (coefficientSobolevOperator period (K i) (coordinateProduct
    period hq i u v))‖ ≤ _
  have h := (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin
    3))) =>
    coordinate_coefficient_reverse_norm period hq (C i) (K i) i u v))
  simpa only [Finset.sum_mul] using h

/-- The actual lower-order nonlinear difference is Lipschitz in L² with only fixed higher Sobolev norms in the coefficient. -/
theorem differenceRemainder_norm {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (t : T)
    (u v : SobolevSpace period (q+1)) :
    ‖value period (differenceRemainder period D hq t u v)‖ ≤
      (((D.linear.coefficient t).bound : ℝ)+
        4*sobolevEmbeddingConstant period q*‖D.approximation t+v‖+
        (∑ i : Fin 3, (((D.quadratic i).coefficient t).bound : ℝ))*sobolevEmbeddingConstant period
          q*
          (‖D.approximation t+u‖+‖D.approximation t+v‖))*‖value period (u-v)‖ := by
  let d := u-v
  let L := velocityComponents D.κ D.direction
  let hL := velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound
  let C := fun i => coefficientSobolevOperator period ((D.quadratic i).jet t)
  have htrans := transport_reverse_norm period hq L hL d (D.approximation t+v)
  have halg1 := algebraic_norm period hq (fun i => (D.quadratic i).coefficient t)
    (fun i => (D.quadratic i).jet t) (D.approximation t+u) d
  have halg2 := algebraic_reverse_norm period hq (fun i => (D.quadratic i).coefficient t)
    (fun i => (D.quadratic i).jet t) d (D.approximation t+v)
  have hlin : ‖value period (coefficientSobolevOperator period (D.linear.jet t) (truncateOperator
    period q d))‖ ≤
      ((D.linear.coefficient t).bound : ℝ)*‖value period d‖ := by
    rw [coefficientSobolevOperator_value,value_truncateOperator]
    exact ((D.linear.coefficient t).operator.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (EulerLiftedPressure.coefficientOperator_norm_le
        (D.linear.coefficient t).coefficient (D.linear.coefficient t).measurable
        (D.linear.coefficient t).bound (D.linear.coefficient t).norm_bound) (norm_nonneg _))
  have hsum : ‖value period (differenceRemainder period D hq t u v)‖ ≤
      ‖value period (transportBilinear period hq L hL d (D.approximation t+v))‖+
      ‖value period (coefficientSobolevOperator period (D.linear.jet t) (truncateOperator period q
        d))‖+
      ‖value period (algebraicBilinear period hq C (D.approximation t+u) d)‖+
      ‖value period (algebraicBilinear period hq C d (D.approximation t+v))‖ := by
    change ‖(_+_+_+_ : LiftL2 period)‖ ≤ _
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
  exact hsum.trans ((add_le_add (add_le_add (add_le_add htrans hlin) halg1) halg2).trans_eq (by
    dsimp [d]; ring))

end EulerCorrectionDifference
