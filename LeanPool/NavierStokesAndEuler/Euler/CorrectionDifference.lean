/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.EulerCorrectionEquation
import LeanPool.NavierStokesAndEuler.Euler.SobolevPressureResolvent
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionOperators

/-! Exact nonlinear correction differences and their genuine L² lower-order bounds. -/

section

/-! Actual L² bounds for the lower-order difference terms in nonlinear transport. -/

@[expose] public section

noncomputable section

namespace EulerSobolevL2Stability

open MeasureTheory EulerLiftedGradientSpace EulerSpatialSobolevInverse EulerCylinderSobolev
  EulerCylinderSobolevSpace EulerSobolevL2Product EulerSobolevTransport EulerCorrectionOperators
  EulerSobolevCoefficientPressure EulerVectorCylinder
open scoped Topology ENNReal

variable (period : ℝ) [Fact (0 < period)]

/-- The actual scalar-vector product is L² bounded in its first input when the second input has
three Sobolev derivatives. -/
theorem scalarProduct_reverse_norm {q : ℕ} (hq : 3 ≤ q) (L : Vector3 →L[ℝ] ℝ)
    (u v : SobolevSpace period q) :
    ‖scalarProduct period hq L u (value period v)‖ ≤
      (‖L‖*sobolevEmbeddingConstant period q)*‖v‖*‖value period u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [scalarProduct_ae period hq L u (value period v),value_ae_bound period hq v] with
      x hp hv
  rw [hp,norm_smul]
  calc
    _ ≤ (‖L‖*‖value period u x‖)*(sobolevEmbeddingConstant period q*‖v‖) :=
      mul_le_mul (L.le_opNorm _) hv (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

/-- Actual nonlinear transport is L² bounded in its advecting input by one higher Sobolev norm of
the advected input. -/
theorem transport_reverse_norm {q : ℕ} (hq : 6 ≤ q)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (q + 1)) :
    ‖value period (transportBilinear period hq L hL u v)‖ ≤
      (4*sobolevEmbeddingConstant period q)*‖v‖*‖value period u‖ := by
  rw [transportBilinear_value]
  have hi (i : Fin 4) : ‖scalarProduct period (by omega : 3 ≤ q) (L i)
      (truncateOperator period q u) (value period (derivativeOperator period q i v))‖ ≤
      sobolevEmbeddingConstant period q*‖v‖*‖value period u‖ := by
    have h := scalarProduct_reverse_norm period (by omega : 3 ≤ q) (L i)
      (truncateOperator period q u) (derivativeOperator period q i v)
    rw [value_truncateOperator] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact mul_le_mul (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right (hL i)
        (sobolevEmbeddingConstant_nonneg period q))) (derivativeOperator_bound period i v)
      (norm_nonneg _) (sobolevEmbeddingConstant_nonneg period q)
  have h := (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin
      4))) => hi i))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat,
      mul_assoc] using h

/-- A genuine coefficient-weighted coordinate product is L² bounded in the vector factor. -/
theorem coordinate_coefficient_norm {q : ℕ} (hq : 6 ≤ q) (C : SmoothCoefficient period)
    (K : CoefficientJet period standardDirection q C) (i : Fin 3)
    (u v : SobolevSpace period (q + 1)) :
    ‖value period (coefficientSobolevOperator period K (coordinateProduct period hq i u v))‖ ≤
      (C.bound*sobolevEmbeddingConstant period q)*‖u‖*‖value period v‖ := by
  rw [coefficientSobolevOperator_value]
  have hp : value period (coordinateProduct period hq i u v) =
      scalarProduct period (by omega : 3 ≤ q) (coordinate 3 i)
        (truncateOperator period q u) (value period (truncateOperator period q v)) :=
    productHq_value period hq (coordinate 3 i) (coordinate_norm_le 3 i) _ _
  rw [hp,value_truncateOperator]
  have hC := C.operator.le_opNorm (scalarProduct period (by omega : 3 ≤ q) (coordinate 3 i)
    (truncateOperator period q u) (value period v))
  have hCn : ‖C.operator‖ ≤ C.bound := EulerLiftedPressure.coefficientOperator_norm_le
    C.coefficient C.measurable C.bound C.norm_bound
  have hs := scalarProduct_norm period (by omega : 3 ≤ q) (coordinate 3 i)
    (truncateOperator period q u) (value period v)
  have hs' : ‖scalarProduct period (by omega : 3 ≤ q) (coordinate 3 i)
      (truncateOperator period q u) (value period v)‖ ≤ sobolevEmbeddingConstant period
          q*‖u‖*‖value period v‖ := by
    apply hs.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact mul_le_mul (by
        simpa only [one_mul] using (mul_le_mul_of_nonneg_right (coordinate_norm_le 3 i)
        (sobolevEmbeddingConstant_nonneg period q))) (truncateOperator_bound period u)
      (norm_nonneg _) (sobolevEmbeddingConstant_nonneg period q)
  exact hC.trans ((mul_le_mul hCn hs' (norm_nonneg _) (by positivity)).trans_eq (by ring))

/-- A genuine coefficient-weighted coordinate product is also L² bounded in its scalar factor. -/
theorem coordinate_coefficient_reverse_norm {q : ℕ} (hq : 6 ≤ q) (C : SmoothCoefficient period)
    (K : CoefficientJet period standardDirection q C) (i : Fin 3)
    (u v : SobolevSpace period (q + 1)) :
    ‖value period (coefficientSobolevOperator period K (coordinateProduct period hq i u v))‖ ≤
      (C.bound*sobolevEmbeddingConstant period q)*‖v‖*‖value period u‖ := by
  rw [coefficientSobolevOperator_value]
  have hp : value period (coordinateProduct period hq i u v) =
      scalarProduct period (by omega : 3 ≤ q) (coordinate 3 i)
        (truncateOperator period q u) (value period (truncateOperator period q v)) :=
    productHq_value period hq (coordinate 3 i) (coordinate_norm_le 3 i) _ _
  rw [hp]
  have hC := C.operator.le_opNorm (scalarProduct period (by omega : 3 ≤ q) (coordinate 3 i)
    (truncateOperator period q u) (value period (truncateOperator period q v)))
  have hCn : ‖C.operator‖ ≤ C.bound := EulerLiftedPressure.coefficientOperator_norm_le
    C.coefficient C.measurable C.bound C.norm_bound
  have hs := scalarProduct_reverse_norm period (by omega : 3 ≤ q) (coordinate 3 i)
    (truncateOperator period q u) (truncateOperator period q v)
  simp only [value_truncateOperator] at hs
  have hs' : ‖scalarProduct period (by omega : 3 ≤ q) (coordinate 3 i)
      (truncateOperator period q u) (value period (truncateOperator period q v))‖ ≤
      sobolevEmbeddingConstant period q*‖v‖*‖value period u‖ := by
    apply hs.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact mul_le_mul (by
        simpa only [one_mul] using (mul_le_mul_of_nonneg_right (coordinate_norm_le 3 i)
        (sobolevEmbeddingConstant_nonneg period q))) (truncateOperator_bound period v)
      (norm_nonneg _) (sobolevEmbeddingConstant_nonneg period q)
  exact hC.trans ((mul_le_mul hCn hs' (norm_nonneg _) (by positivity)).trans_eq (by ring))

end EulerSobolevL2Stability

end
end

end

@[expose] public section

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
    (u v : SobolevSpace period (q + 1)) : SobolevSpace period q :=
  transportBilinear period hq (velocityComponents D.κ D.direction)
    (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound) (u-v)
        (D.approximation t+v) +
    coefficientSobolevOperator period (D.linear.jet t) (truncateOperator period q (u-v)) +
    algebraicBilinear period hq (fun i => coefficientSobolevOperator period ((D.quadratic i).jet t))
      (D.approximation t+u) (u-v) +
    algebraicBilinear period hq (fun i => coefficientSobolevOperator period ((D.quadratic i).jet t))
      (u-v) (D.approximation t+v)

/-- Exact bilinear subtraction exposes one cancellable top transport and the actual lower-order
difference. -/
theorem rawSource_sub {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (t : T)
    (u v : SobolevSpace period (q + 1)) :
    D.rawSource period hq t u-D.rawSource period hq t v =
      transportBilinear period hq (velocityComponents D.κ D.direction)
        (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound) (D.approximation
            t+u) (u-v) +
      differenceRemainder period D hq t u v := by
  let B := eulerBilinear period hq (velocityComponents D.κ D.direction)
    (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound)
    (fun i => coefficientSobolevOperator period ((D.quadratic i).jet t))
  let A := (coefficientSobolevOperator period (D.linear.jet t)).comp (truncateOperator period q)
  change (D.residual t+linearize B A (D.approximation t) u+B u u) -
    (D.residual t+linearize B A (D.approximation t) v+B v v)=_
  dsimp only [B,A]
  simp only [differenceRemainder,linearize_apply,eulerBilinear,add_apply,map_add,map_sub,sub_apply,
    ContinuousLinearMap.comp_apply]
  abel

/-- The actual algebraic quadratic term has an L² bound in its second input. -/
theorem algebraic_norm {q : ℕ} (hq : 6 ≤ q) (C : Fin 3 → SmoothCoefficient period)
    (K : ∀ i, CoefficientJet period standardDirection q (C i))
    (u v : SobolevSpace period (q + 1)) :
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
    (u v : SobolevSpace period (q + 1)) :
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

/-- The actual lower-order nonlinear difference is Lipschitz in L² with only fixed higher Sobolev
norms in the coefficient. -/
theorem differenceRemainder_norm {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (t : T)
    (u v : SobolevSpace period (q + 1)) :
    ‖value period (differenceRemainder period D hq t u v)‖ ≤
      (((D.linear.coefficient t).bound : ℝ) +
        4*sobolevEmbeddingConstant period q*‖D.approximation t+v‖+
        (∑ i : Fin 3, (((D.quadratic i).coefficient t).bound : ℝ))*sobolevEmbeddingConstant period
            q *
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
