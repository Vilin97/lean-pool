/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuOperator.CoeffOperator
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuAdmissibility
public import LeanPool.CoarseGraining.Homogenization.Probability.LocalEllipticitySlices
public import Mathlib.Topology.Order.IsLUB

/-! # Coeff Operator Data -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# A.e.-elliptic coefficient-operator realization data

This file begins the Chapter 4 Phase 3 replacement for the pointwise
`MuOperatorSystemData` handoff.  The old deterministic package is built from
pointwise `IsEllipticFieldOn`; the manuscript-facing support data is only
spatial-a.e. elliptic.  The structures below therefore store a measurable
operator representative together with its a.e. agreement with the raw
normalized coefficient operator.
-/

/--
Measurable representative data for the normalized doubled coefficient operator
when the coefficient field is controlled only up to spatial null sets.

The pointwise `field` is the object used to build the `L²` operator.  The
`ae_eq_normalizedBlockCoeffOperator` field records that this representative is
the same as the raw Ch4 coefficient operator on the observation set, modulo the
restricted volume measure.
-/
structure AEEMuCoeffOperatorData {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) where
  /-- Measurability of the underlying domain. -/
  measurableSet_domain : MeasurableSet U
  /-- A measurable representative of the normalized coefficient operator. -/
  field : Vec d → HilbertBlockVec d →L[ℝ] HilbertBlockVec d
  /-- Measurability of the representative operator field. -/
  measurable_field : Measurable field
  /-- The representative agrees a.e. with the raw normalized coefficient operator. -/
  ae_eq_normalizedBlockCoeffOperator :
    field =ᵐ[volumeMeasureOn U] normalizedBlockCoeffOperator U a
  /-- A uniform operator-norm bound for the representative. -/
  opNormBound : ℝ
  /-- Nonnegativity of the bound. -/
  opNormBound_nonneg : 0 ≤ opNormBound
  /-- The representative operators are bounded by `opNormBound`. -/
  le_opNormBound : ∀ x : Vec d, ‖field x‖ ≤ opNormBound
  /-- Coercivity constant for the induced `L²` operator. -/
  coercivityConstant : ℝ
  /-- Positivity of the coercivity constant. -/
  coercivityConstant_pos : 0 < coercivityConstant
  /-- A.e. symmetry of the pointwise representative. -/
  ae_field_inner_comm :
    ∀ᵐ x ∂ volumeMeasureOn U,
      ∀ X Y : HilbertBlockVec d, inner ℝ (field x X) Y = inner ℝ X (field x Y)
  /-- A.e. pointwise coercivity of the representative. -/
  ae_field_self_inner_lowerBound :
    ∀ᵐ x ∂ volumeMeasureOn U,
      ∀ X : HilbertBlockVec d,
        coercivityConstant * inner ℝ X X ≤ inner ℝ (field x X) X

namespace AEEMuCoeffOperatorData

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}

/-- Forget the a.e. identification data and keep the measurable bounded
representative as a pointwise operator field. -/
def toPointwiseField (M : AEEMuCoeffOperatorData U a) :
    PointwiseHilbertBlockOperatorField U where
  field := M.field
  measurable_field := M.measurable_field
  opNormBound := M.opNormBound
  opNormBound_nonneg := M.opNormBound_nonneg
  le_opNormBound := M.le_opNormBound

/-- The bounded `L²` operator induced by the measurable representative. -/
noncomputable def operator (M : AEEMuCoeffOperatorData U a) :
    HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U :=
  M.toPointwiseField.toContinuousLinearMap

/-- Pointwise a.e. description of the representative-induced `L²` operator. -/
theorem ae_apply_operator (M : AEEMuCoeffOperatorData U a)
    (F : HilbertBlockL2 U) :
    M.operator F =ᵐ[volumeMeasureOn U] fun x => M.field x (F x) :=
  M.toPointwiseField.coeFn_toContinuousLinearMap F

/-- The representative-induced `L²` operator agrees a.e. with the raw
normalized coefficient operator applied to `F`. -/
theorem ae_apply_operator_normalizedBlockCoeffOperator
    (M : AEEMuCoeffOperatorData U a) (F : HilbertBlockL2 U) :
    M.operator F =ᵐ[volumeMeasureOn U]
      fun x => normalizedBlockCoeffOperator U a x (F x) := by
  filter_upwards [M.ae_apply_operator F, M.ae_eq_normalizedBlockCoeffOperator]
    with x hOp hEq
  rw [hOp, hEq]

/-- Symmetry of the `L²` operator induced by the a.e.-symmetric representative. -/
theorem operatorSymm (M : AEEMuCoeffOperatorData U a) :
    LinearMap.IsSymmetric (M.operator : HilbertBlockL2 U →ₗ[ℝ] HilbertBlockL2 U) := by
  intro F G
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [M.ae_apply_operator F, M.ae_apply_operator G, M.ae_field_inner_comm]
    with x hF hG hsymm
  simpa [hF, hG] using hsymm (F x) (G x)

/-- Coercivity of the `L²` operator induced by the a.e.-coercive representative. -/
theorem operatorCoercive (M : AEEMuCoeffOperatorData U a) :
    IsCoercive (energyBilinOfOperator M.operator) := by
  refine ⟨M.coercivityConstant, M.coercivityConstant_pos, ?_⟩
  intro F
  have hleftInt :
      MeasureTheory.Integrable (fun x =>
        M.coercivityConstant * inner ℝ (F x) (F x)) (volumeMeasureOn U) := by
    exact (MeasureTheory.L2.integrable_inner F F).const_mul M.coercivityConstant
  have hrightInt :
      MeasureTheory.Integrable (fun x =>
        inner ℝ ((M.operator F) x) (F x)) (volumeMeasureOn U) := by
    exact MeasureTheory.L2.integrable_inner (M.operator F) F
  have hmono :
      ∀ᵐ x ∂ volumeMeasureOn U,
        M.coercivityConstant * inner ℝ (F x) (F x) ≤
          inner ℝ ((M.operator F) x) (F x) := by
    filter_upwards [M.ae_apply_operator F, M.ae_field_self_inner_lowerBound]
      with x hOp hpoint
    rw [hOp]
    exact hpoint (F x)
  calc
    M.coercivityConstant * ‖F‖ * ‖F‖
        = ∫ x, M.coercivityConstant * inner ℝ (F x) (F x) ∂ volumeMeasureOn U := by
            have hnorm :
                ‖F‖ * ‖F‖ =
                  ∫ x, inner ℝ (F x) (F x) ∂ volumeMeasureOn U := by
              calc
                ‖F‖ * ‖F‖ = ‖F‖ ^ 2 := by ring
                _ = inner ℝ F F := by
                  symm
                  exact real_inner_self_eq_norm_sq F
                _ = ∫ x, inner ℝ (F x) (F x) ∂ volumeMeasureOn U := by
                  rw [MeasureTheory.L2.inner_def]
            calc
              M.coercivityConstant * ‖F‖ * ‖F‖ =
                  M.coercivityConstant * (‖F‖ * ‖F‖) := by ring
              _ = M.coercivityConstant *
                    ∫ x, inner ℝ (F x) (F x) ∂ volumeMeasureOn U := by
                    rw [hnorm]
              _ = ∫ x, M.coercivityConstant * inner ℝ (F x) (F x)
                    ∂ volumeMeasureOn U := by
                    rw [← MeasureTheory.integral_const_mul]
    _ ≤ ∫ x, inner ℝ ((M.operator F) x) (F x) ∂ volumeMeasureOn U := by
          exact MeasureTheory.integral_mono_ae hleftInt hrightInt hmono
    _ = energyBilinOfOperator M.operator F F := by
          rw [energyBilinOfOperator_apply, MeasureTheory.L2.inner_def]

/-- Package the a.e.-representative data as the concrete `Mu` operator
realization expected by the Hilbert minimization layer. -/
noncomputable def toMuOperatorRealization (M : AEEMuCoeffOperatorData U a) :
    MuOperatorRealization U a where
  operator := M.operator
  ae_apply := by
    intro F
    filter_upwards
        [M.ae_apply_operator_normalizedBlockCoeffOperator F,
         MeasureTheory.ae_restrict_of_forall_mem M.measurableSet_domain
           (fun x hx => normalizedBlockCoeffOperator_apply_of_mem a hx (F x))]
      with x hOp hEq
    rw [hOp, hEq]
  operatorSymm := M.operatorSymm
  operatorCoercive := M.operatorCoercive

private theorem le_normalizedBlockCoeffOperatorNormBound_of_isEllipticMatrix_of_mem
    {lam Lam : ℝ} {x : Vec d} (hx : x ∈ U)
    (hmat : IsEllipticMatrix lam Lam (a x)) :
    ‖normalizedBlockCoeffOperator U a x‖ ≤
      MuCoeffOperatorData.normalizedBlockCoeffOperatorNormBound (d := d) U lam Lam := by
  have hA :
      ‖HilbertBlockVec.applyBlockMat (blockCoeffField a x)‖ ≤
        Real.sqrt (blockMatrixOfCoeffNormSqBound lam Lam) := by
    apply HilbertBlockVec.opNorm_applyBlockMat_le_of_block_bound
    · exact Real.sqrt_nonneg _
    · intro X
      have hbound := blockMatrixOfCoeff_image_bound_of_isEllipticMatrix hmat X
      calc
        blockVecDot (blockMatVecMul (blockCoeffField a x) X)
            (blockMatVecMul (blockCoeffField a x) X)
            ≤ blockMatrixOfCoeffNormSqBound lam Lam * blockVecDot X X := hbound
        _ = (Real.sqrt (blockMatrixOfCoeffNormSqBound lam Lam)) ^ 2 * blockVecDot X X := by
          rw [Real.sq_sqrt (blockMatrixOfCoeffNormSqBound_nonneg lam Lam)]
  rw [MuCoeffOperatorData.normalizedBlockCoeffOperator_eq_of_mem (U := U) a hx]
  calc
    ‖(MeasureTheory.volume U).toReal⁻¹ •
        HilbertBlockVec.applyBlockMat (blockCoeffField a x)‖
        ≤ ‖(MeasureTheory.volume U).toReal⁻¹‖ *
          ‖HilbertBlockVec.applyBlockMat (blockCoeffField a x)‖ := by
            exact
              norm_smul_le
                (MeasureTheory.volume U).toReal⁻¹
                (HilbertBlockVec.applyBlockMat (blockCoeffField a x))
    _ ≤ ‖(MeasureTheory.volume U).toReal⁻¹‖ *
          Real.sqrt (blockMatrixOfCoeffNormSqBound lam Lam) := by
        exact mul_le_mul_of_nonneg_left hA (norm_nonneg _)
    _ = MuCoeffOperatorData.normalizedBlockCoeffOperatorNormBound (d := d) U lam Lam := by
        simp [MuCoeffOperatorData.normalizedBlockCoeffOperatorNormBound]

private theorem normalizedBlockCoeffOperator_self_inner_lowerBound_of_isEllipticMatrix_of_mem
    {lam Lam : ℝ} {x : Vec d} (hx : x ∈ U)
    (hmat : IsEllipticMatrix lam Lam (a x)) (X : HilbertBlockVec d) :
    ((MeasureTheory.volume U).toReal⁻¹ * (lam / (1 + 2 * Lam ^ 2))) * inner ℝ X X ≤
      inner ℝ (normalizedBlockCoeffOperator U a x X) X := by
  have hcoer :
      (lam / (1 + 2 * Lam ^ 2)) * blockVecDot X.toBlockVec X.toBlockVec ≤
        blockVecDot X.toBlockVec
          (blockMatVecMul (blockCoeffField a x) X.toBlockVec) := by
    simpa [blockCoeffField] using
      (blockMatrixOfCoeff_coercive_of_isEllipticMatrix hmat X.toBlockVec)
  have hvol_nonneg : 0 ≤ (MeasureTheory.volume U).toReal⁻¹ := by
    positivity
  have htoBlock :
      (((MeasureTheory.volume U).toReal⁻¹ •
          HilbertBlockVec.ofBlockVec (blockMatVecMul (blockCoeffField a x) X.toBlockVec)).toBlockVec) =
        (MeasureTheory.volume U).toReal⁻¹ •
          blockMatVecMul (blockCoeffField a x) X.toBlockVec := by
    ext i <;> simp [HilbertVec.toVec, mul_add]
  rw [normalizedBlockCoeffOperator_apply_of_mem a hx X]
  calc
    ((MeasureTheory.volume U).toReal⁻¹ * (lam / (1 + 2 * Lam ^ 2))) * inner ℝ X X
        = (MeasureTheory.volume U).toReal⁻¹ *
            ((lam / (1 + 2 * Lam ^ 2)) * blockVecDot X.toBlockVec X.toBlockVec) := by
              simp [mul_assoc, mul_left_comm, mul_comm]
    _ ≤ (MeasureTheory.volume U).toReal⁻¹ *
          blockVecDot X.toBlockVec
            (blockMatVecMul (blockCoeffField a x) X.toBlockVec) := by
          exact mul_le_mul_of_nonneg_left hcoer hvol_nonneg
    _ = inner ℝ X ((MeasureTheory.volume U).toReal⁻¹ •
          HilbertBlockVec.applyBlockMat (blockCoeffField a x) X) := by
          rw [HilbertBlockVec.inner_def, HilbertBlockVec.applyBlockMat_apply, htoBlock,
            blockVecDot_smul_right]
    _ = inner ℝ ((MeasureTheory.volume U).toReal⁻¹ •
          HilbertBlockVec.applyBlockMat (blockCoeffField a x) X) X := by
          rw [real_inner_comm]

/-- Build a.e.-representative coefficient-operator data from spatial-a.e.
ellipticity on `U`.  The representative is obtained coordinatewise from
`AEStronglyMeasurable.mk`, then clamped to the deterministic ellipticity norm
bound; the clamping is invisible a.e. on the elliptic support. -/
noncomputable def ofIsAEEllipticFieldOn {lam Lam : ℝ}
    (hEll : IsAEEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal) :
    AEEMuCoeffOperatorData U a := by
  classical
  let A : Vec d → Mat d := fun x i j =>
    (hEll.aestronglyMeasurable_restrictCoeffField_apply i j).mk
      (fun x : Vec d => restrictCoeffField U a x i j) x
  have hA_meas : Measurable A := by
    refine measurable_pi_iff.2 ?_
    intro i
    refine measurable_pi_iff.2 ?_
    intro j
    exact (hEll.aestronglyMeasurable_restrictCoeffField_apply i j).measurable_mk
  have hentries : ∀ᵐ x ∂ volumeMeasureOn U,
      ∀ i j : Fin d, A x i j = restrictCoeffField U a x i j := by
    exact eventually_countable_forall.mpr fun i : Fin d =>
      eventually_countable_forall.mpr fun j : Fin d =>
        (hEll.aestronglyMeasurable_restrictCoeffField_apply i j).ae_eq_mk.symm
  have hA_eq : A =ᵐ[volumeMeasureOn U] fun x => restrictCoeffField U a x := by
    filter_upwards [hentries] with x hx
    funext i j
    exact hx i j
  let op0 : Vec d → HilbertBlockVec d →L[ℝ] HilbertBlockVec d := fun x =>
    (MeasureTheory.volume U).toReal⁻¹ •
      HilbertBlockVec.applyBlockMat (blockMatrixOfCoeff (A x))
  have hop0_meas : Measurable op0 := by
    have hfull : Measurable (fun x : Vec d => fun α β =>
        toFullBlockMat (blockMatrixOfCoeff (A x)) α β) := by
      exact measurable_toFullBlockMat_blockCoeffField hA_meas
    have hmeas : Measurable (fun x : Vec d =>
        fullEntriesToHilbertOperator d (toFullBlockMat (blockMatrixOfCoeff (A x)))) := by
      exact measurable_fullEntriesToHilbertOperator hfull
    have hsmul : Measurable (fun x : Vec d =>
        (MeasureTheory.volume U).toReal⁻¹ •
          fullEntriesToHilbertOperator d (toFullBlockMat (blockMatrixOfCoeff (A x)))) :=
      hmeas.const_smul ((MeasureTheory.volume U).toReal⁻¹)
    simpa [op0, fullEntriesToHilbertOperator_toFullBlockMat] using hsmul
  have hop0_eq_raw : op0 =ᵐ[volumeMeasureOn U] normalizedBlockCoeffOperator U a := by
    filter_upwards [hA_eq] with x hx
    apply ContinuousLinearMap.ext
    intro X
    ext i <;> simp [op0, normalizedBlockCoeffOperator, blockCoeffField, hx,
      HilbertBlockVec.applyBlockMat_apply]
  let K : ℝ := MuCoeffOperatorData.normalizedBlockCoeffOperatorNormBound (d := d) U lam Lam
  let field : Vec d → HilbertBlockVec d →L[ℝ] HilbertBlockVec d := fun x =>
    if ‖op0 x‖ ≤ K then op0 x else (0 : HilbertBlockVec d →L[ℝ] HilbertBlockVec d)
  have hfield_meas : Measurable field := by
    have hset : MeasurableSet {x : Vec d | ‖op0 x‖ ≤ K} := by
      exact measurableSet_le (continuous_norm.measurable.comp hop0_meas) measurable_const
    exact Measurable.ite hset hop0_meas measurable_const
  have hK_nonneg : 0 ≤ K :=
    MuCoeffOperatorData.normalizedBlockCoeffOperatorNormBound_nonneg (d := d) U lam Lam
  have hraw_bound : ∀ᵐ x ∂ volumeMeasureOn U,
      ‖normalizedBlockCoeffOperator U a x‖ ≤ K := by
    filter_upwards [MeasureTheory.ae_restrict_mem hEll.measurableSet,
      hEll.ae_isEllipticMatrix] with x hxU hxEll
    exact le_normalizedBlockCoeffOperatorNormBound_of_isEllipticMatrix_of_mem
      (U := U) (a := a) hxU hxEll
  have hfield_eq_raw : field =ᵐ[volumeMeasureOn U] normalizedBlockCoeffOperator U a := by
    filter_upwards [hop0_eq_raw, hraw_bound] with x hop0_eq hbound
    have hop0_bound : ‖op0 x‖ ≤ K := by
      rwa [hop0_eq]
    have hfield_x : field x = op0 x := by
      change (if ‖op0 x‖ ≤ K then op0 x
        else (0 : HilbertBlockVec d →L[ℝ] HilbertBlockVec d)) = op0 x
      exact if_pos hop0_bound
    rw [hfield_x, hop0_eq]
  have hvol_ne_zero : MeasureTheory.volume U ≠ 0 := by
    intro hzero
    rw [hzero] at hvol
    simp at hvol
  have hlam_pos : 0 < lam := by
    obtain ⟨x, _hxU, hxEll⟩ :=
      MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae
        (μ := MeasureTheory.volume) (s := U) hvol_ne_zero hEll.ae_isEllipticMatrix
    exact hxEll.1
  let C : ℝ := (MeasureTheory.volume U).toReal⁻¹ * (lam / (1 + 2 * Lam ^ 2))
  have hC_pos : 0 < C := by
    have hvolInv : 0 < (MeasureTheory.volume U).toReal⁻¹ := by
      positivity
    have hden : 0 < 1 + 2 * Lam ^ 2 := by
      nlinarith [sq_nonneg Lam]
    exact mul_pos hvolInv (div_pos hlam_pos hden)
  exact
    { measurableSet_domain := hEll.measurableSet
      field := field
      measurable_field := hfield_meas
      ae_eq_normalizedBlockCoeffOperator := hfield_eq_raw
      opNormBound := K
      opNormBound_nonneg := hK_nonneg
      le_opNormBound := by
        intro x
        by_cases hx : ‖op0 x‖ ≤ K
        · have hfield_x : field x = op0 x := by
            change (if ‖op0 x‖ ≤ K then op0 x
              else (0 : HilbertBlockVec d →L[ℝ] HilbertBlockVec d)) = op0 x
            exact if_pos hx
          rw [hfield_x]
          exact hx
        · have hfield_x : field x = 0 := by
            change (if ‖op0 x‖ ≤ K then op0 x
              else (0 : HilbertBlockVec d →L[ℝ] HilbertBlockVec d)) =
                (0 : HilbertBlockVec d →L[ℝ] HilbertBlockVec d)
            exact if_neg hx
          rw [hfield_x]
          rw [norm_zero]
          exact hK_nonneg
      coercivityConstant := C
      coercivityConstant_pos := hC_pos
      ae_field_inner_comm := by
        filter_upwards [hfield_eq_raw] with x hEq X Y
        rw [hEq]
        exact MuCoeffOperatorData.normalizedBlockCoeffOperator_inner_comm
          (U := U) (a := a) x X Y
      ae_field_self_inner_lowerBound := by
        filter_upwards [hfield_eq_raw, MeasureTheory.ae_restrict_mem hEll.measurableSet,
          hEll.ae_isEllipticMatrix] with x hEq hxU hxEll X
        rw [hEq]
        exact normalizedBlockCoeffOperator_self_inner_lowerBound_of_isEllipticMatrix_of_mem
          (U := U) (a := a) hxU hxEll X }

/-- The old pointwise deterministic coefficient-operator data embeds in the new
a.e.-representative package. -/
noncomputable def ofMuCoeffOperatorDataOfIsEllipticFieldOn
    (M : MuCoeffOperatorData U a) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal) :
    AEEMuCoeffOperatorData U a where
  measurableSet_domain := M.measurableSet_domain
  field := normalizedBlockCoeffOperator U a
  measurable_field := M.measurable_normalizedBlockCoeffOperator
  ae_eq_normalizedBlockCoeffOperator := Filter.EventuallyEq.rfl
  opNormBound := M.opNormBound
  opNormBound_nonneg := M.opNormBound_nonneg
  le_opNormBound := M.le_opNormBound
  coercivityConstant :=
    (MeasureTheory.volume U).toReal⁻¹ * (lam / (1 + 2 * Lam ^ 2))
  coercivityConstant_pos := by
    have hlam : 0 < lam :=
      MuCoeffOperatorData.lam_pos_of_isEllipticFieldOn
        (U := U) (a := a) hEll hvol
    have hvolInv : 0 < (MeasureTheory.volume U).toReal⁻¹ := by
      positivity
    have hden : 0 < 1 + 2 * Lam ^ 2 := by
      nlinarith [sq_nonneg Lam]
    exact mul_pos hvolInv (div_pos hlam hden)
  ae_field_inner_comm :=
    Filter.Eventually.of_forall
      (fun x => MuCoeffOperatorData.normalizedBlockCoeffOperator_inner_comm
        (U := U) (a := a) x)
  ae_field_self_inner_lowerBound :=
    MeasureTheory.ae_restrict_of_forall_mem M.measurableSet_domain
      (fun x hx =>
        MuCoeffOperatorData.normalizedBlockCoeffOperator_self_inner_lowerBound_of_mem
          (U := U) (a := a) hEll hx)

end AEEMuCoeffOperatorData

/--
A.e.-representative operator-system data for the doubled `\mu` problem on `U`.

This is the Phase 3 target API: it has the same Hilbert-minimization output as
`MuOperatorSystemData`, but its coefficient operator is allowed to be a
measurable representative of the raw coefficient field.
-/
structure AEEMuOperatorSystemData {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) where
  /-- The closed correction space `\Lpoto(U) × \Lsolo(U)`. -/
  correctionSpace : MuCorrectionSpaceData U
  /-- A.e.-representative coefficient-operator data. -/
  coeffOperatorData : AEEMuCoeffOperatorData U a

namespace AEEMuOperatorSystemData

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}

/-- The concrete doubled operator realization extracted from the AEE system
package. -/
noncomputable def toMuOperatorRealization (M : AEEMuOperatorSystemData U a) :
    MuOperatorRealization U a :=
  M.coeffOperatorData.toMuOperatorRealization

/-- The concrete Hilbert-space realization of the doubled `\mu` problem
extracted from the AEE system package. -/
noncomputable def toMuHilbertRealization
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (M : AEEMuOperatorSystemData U a) :
    MuHilbertRealization U a :=
  M.toMuOperatorRealization.toMuHilbertRealization M.correctionSpace

end AEEMuOperatorSystemData

namespace MuHilbertRealization

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}

/-- The Hilbert minimizer value is the infimum of the quadratic energy over the
whole affine correction space. -/
theorem muCandidate_eq_sInf_quadraticEnergy_correctionSpace
    (H : MuHilbertRealization U a) (P : BlockVec d) :
    H.muCandidate P =
      sInf (Set.range fun Y : H.correctionSpace.correctionSpace.toSubmodule =>
        quadraticEnergy H.energyBilin (H.constantField P + (Y : HilbertBlockL2 U))) := by
  let f : H.correctionSpace.correctionSpace.toSubmodule → ℝ := fun Y =>
    quadraticEnergy H.energyBilin (H.constantField P + (Y : HilbertBlockL2 U))
  let s : Set ℝ := Set.range f
  have hs_nonempty : s.Nonempty := by
    refine ⟨f ⟨H.minimizerMap P - H.constantField P, H.sub_minimizerMap_apply_mem P⟩, ?_⟩
    exact ⟨⟨H.minimizerMap P - H.constantField P, H.sub_minimizerMap_apply_mem P⟩, rfl⟩
  have h_lower : ∀ m ∈ s, H.muCandidate P ≤ m := by
    intro m hm
    rcases hm with ⟨Y, rfl⟩
    have hcorr :
        H.constantField P + (Y : HilbertBlockL2 U) - H.constantField P ∈
          H.correctionSpace.correctionSpace := by
      have hsub :
          H.constantField P + (Y : HilbertBlockL2 U) - H.constantField P =
            (Y : HilbertBlockL2 U) := by
        abel
      rw [hsub]
      exact Y.property
    simpa [f] using H.muCandidate_le_quadraticEnergy P
      (H.constantField P + (Y : HilbertBlockL2 U)) hcorr
  have hs_bddBelow : BddBelow s := ⟨H.muCandidate P, h_lower⟩
  apply le_antisymm
  · exact le_csInf hs_nonempty h_lower
  · have hmem :
        f ⟨H.minimizerMap P - H.constantField P,
            H.sub_minimizerMap_apply_mem P⟩ ∈ s := by
      exact ⟨⟨H.minimizerMap P - H.constantField P, H.sub_minimizerMap_apply_mem P⟩, rfl⟩
    calc
      sInf s ≤
          f ⟨H.minimizerMap P - H.constantField P,
              H.sub_minimizerMap_apply_mem P⟩ := csInf_le hs_bddBelow hmem
      _ = H.muCandidate P := by
        have hadd :
            H.constantField P + (H.minimizerMap P - H.constantField P) =
              H.minimizerMap P := by
          abel
        change quadraticEnergy H.energyBilin
            (H.constantField P + (H.minimizerMap P - H.constantField P)) =
          H.muCandidate P
        rw [hadd]
        rfl

/-- Dense correction-space subsets may be used to compute the Hilbert minimizer
value. -/
theorem muCandidate_eq_sInf_quadraticEnergy_denseRange
    (H : MuHilbertRealization U a) (P : BlockVec d)
    {β : Type*} [TopologicalSpace β] [Nonempty β]
    (g : β → H.correctionSpace.correctionSpace.toSubmodule)
    (hg : DenseRange g) :
    H.muCandidate P =
      sInf (Set.range fun Y : β =>
        quadraticEnergy H.energyBilin (H.constantField P + (g Y : HilbertBlockL2 U))) := by
  let f : H.correctionSpace.correctionSpace.toSubmodule → ℝ := fun Y =>
    quadraticEnergy H.energyBilin (H.constantField P + (Y : HilbertBlockL2 U))
  let s : Set ℝ := Set.range fun Y : β => f (g Y)
  let t : Set ℝ := Set.range f
  have hs_nonempty : s.Nonempty := by
    refine ⟨f (g (Classical.arbitrary β)), ?_⟩
    exact ⟨Classical.arbitrary β, rfl⟩
  have hs_subset : s ⊆ t := by
    rintro x ⟨Y, rfl⟩
    exact ⟨g Y, rfl⟩
  have h_dense : Dense (Set.range g) := hg
  have h_image_eq : f '' Set.range g = s := by
    ext x
    constructor
    · rintro ⟨Y, ⟨Z, rfl⟩, rfl⟩
      exact ⟨Z, rfl⟩
    · rintro ⟨Y, rfl⟩
      exact ⟨g Y, ⟨Y, rfl⟩, rfl⟩
  have hf : Continuous f := by
    apply (quadraticEnergy_continuous H.energyBilin).comp
    have h : Continuous (fun Y : H.correctionSpace.correctionSpace.toSubmodule =>
        H.constantField P + (Y : HilbertBlockL2 U)) :=
      continuous_const.add continuous_subtype_val
    simpa [f] using h
  have ht_subset_closure : t ⊆ closure s := by
    rw [← h_image_eq]
    simpa [f, t] using hf.range_subset_closure_image_dense h_dense
  have ht_nonempty : t.Nonempty := by
    refine ⟨f ⟨H.minimizerMap P - H.constantField P, H.sub_minimizerMap_apply_mem P⟩, ?_⟩
    exact ⟨⟨H.minimizerMap P - H.constantField P, H.sub_minimizerMap_apply_mem P⟩, rfl⟩
  have h_lower : ∀ m ∈ t, H.muCandidate P ≤ m := by
    intro m hm
    rcases hm with ⟨Y, rfl⟩
    have hcorr :
        H.constantField P + (Y : HilbertBlockL2 U) - H.constantField P ∈
          H.correctionSpace.correctionSpace := by
      have hsub :
          H.constantField P + (Y : HilbertBlockL2 U) - H.constantField P =
            (Y : HilbertBlockL2 U) := by
        abel
      rw [hsub]
      exact Y.property
    simpa [f] using H.muCandidate_le_quadraticEnergy P
      (H.constantField P + (Y : HilbertBlockL2 U)) hcorr
  have ht_bddBelow : BddBelow t := ⟨H.muCandidate P, h_lower⟩
  have ht_isGLB : IsGLB t (H.muCandidate P) := by
    rw [H.muCandidate_eq_sInf_quadraticEnergy_correctionSpace P]
    exact isGLB_csInf ht_nonempty ht_bddBelow
  have hs_isGLB : IsGLB s (H.muCandidate P) :=
    (isGLB_iff_of_subset_of_subset_closure hs_subset ht_subset_closure).2 ht_isGLB
  symm
  exact hs_isGLB.csInf_eq hs_nonempty

end MuHilbertRealization

namespace PotentialSolenoidalL2Data

variable {d : ℕ} {U : Set (Vec d)}

/-- Transport an element of the closed block correction space into the Hilbert
correction space. -/
noncomputable def submoduleClosureToMuCorrectionSpace
    (M : PotentialSolenoidalL2Data U) :
    M.blockPotentialZeroTraceSolenoidalZeroNormalTrace.toSubmodule →
      M.toMuCorrectionSpaceData.correctionSpace.toSubmodule :=
  fun X => ⟨blockL2ToHilbertBlockL2 (U := U) X, by
    show
      hilbertBlockL2ToBlockL2 (U := U)
          (blockL2ToHilbertBlockL2 (U := U) X) ∈
        M.blockPotentialZeroTraceSolenoidalZeroNormalTrace
    rw [hilbertBlockL2ToBlockL2_blockL2ToHilbertBlockL2]
    exact X.property⟩

theorem continuous_submoduleClosureToMuCorrectionSpace
    (M : PotentialSolenoidalL2Data U) :
    Continuous (M.submoduleClosureToMuCorrectionSpace) := by
  apply Continuous.subtype_mk
  exact (blockL2ToHilbertBlockL2 (U := U)).continuous.comp continuous_subtype_val

theorem surjective_submoduleClosureToMuCorrectionSpace
    (M : PotentialSolenoidalL2Data U) :
    Function.Surjective M.submoduleClosureToMuCorrectionSpace := by
  intro Y
  refine ⟨⟨hilbertBlockL2ToBlockL2 (U := U) Y, Y.property⟩, ?_⟩
  apply Subtype.ext
  change
    blockL2ToHilbertBlockL2 (U := U)
        (hilbertBlockL2ToBlockL2 (U := U) (Y : HilbertBlockL2 U)) =
      Y
  exact blockL2ToHilbertBlockL2_hilbertBlockL2ToBlockL2 (U := U) Y

end PotentialSolenoidalL2Data

section CanonicalClosureGenerator

variable {d : ℕ} {U : Set (Vec d)}

/-- The predicate-generated block correction submodule before topological
closure. -/
abbrev canonicalMuBlockCorrectionGeneratorSubmodule (U : Set (Vec d)) :
    Submodule ℝ (BlockL2 U) :=
  PotentialSolenoidalL2Data.blockPotentialZeroTraceSolenoidalZeroNormalTraceSubmodule U

/-- Embed predicate-generated block corrections into the canonical Hilbert
correction space. -/
noncomputable def canonicalMuCorrectionGeneratorEmbedding (U : Set (Vec d)) :
    canonicalMuBlockCorrectionGeneratorSubmodule U →
      (MuCorrectionSpaceData.ofSubmoduleClosures U).correctionSpace.toSubmodule :=
  by
    intro Y
    exact
      (PotentialSolenoidalL2Data.ofSubmoduleClosures U).submoduleClosureToMuCorrectionSpace
        ⟨Y, by
          change (Y : BlockL2 U) ∈
            (PotentialSolenoidalL2Data.blockPotentialZeroTraceSolenoidalZeroNormalTraceSubmodule U).closure
          exact subset_closure Y.property⟩

theorem denseRange_canonicalMuCorrectionGeneratorEmbedding (U : Set (Vec d)) :
    DenseRange (canonicalMuCorrectionGeneratorEmbedding U) := by
  let M : PotentialSolenoidalL2Data U := PotentialSolenoidalL2Data.ofSubmoduleClosures U
  let S : Set (BlockL2 U) :=
    (PotentialSolenoidalL2Data.blockPotentialZeroTraceSolenoidalZeroNormalTraceSubmodule U :
      Set (BlockL2 U))
  let T : Set (BlockL2 U) :=
    ((PotentialSolenoidalL2Data.blockPotentialZeroTraceSolenoidalZeroNormalTraceSubmodule U).closure :
      Set (BlockL2 U))
  let incl : S → T := Set.inclusion (by
    intro x hx
    exact subset_closure hx)
  let post : T → (MuCorrectionSpaceData.ofSubmoduleClosures U).correctionSpace.toSubmodule :=
    fun X => M.submoduleClosureToMuCorrectionSpace X
  have hincl : DenseRange incl := by
    rw [denseRange_inclusion_iff]
    all_goals
      first
        | (intro x hx; exact hx)
        | (intro x hx; exact subset_closure hx)
  have hpost : DenseRange post := by
    have hsurj : Function.Surjective post := by
      intro Y
      rcases M.surjective_submoduleClosureToMuCorrectionSpace Y with ⟨X, hX⟩
      refine ⟨⟨X, X.property⟩, ?_⟩
      exact hX
    exact hsurj.denseRange
  have hpost_cont : Continuous post := by
    exact M.continuous_submoduleClosureToMuCorrectionSpace
  have hcomp : DenseRange (post ∘ incl) := DenseRange.comp hpost hincl hpost_cont
  have hfun : (post ∘ incl) = fun Y => canonicalMuCorrectionGeneratorEmbedding U Y := by
    funext Y
    rfl
  rw [hfun] at hcomp
  exact hcomp

/-- A pointwise representative for one predicate-generated canonical block
correction.  This is intentionally weaker than full recovery data: it only
chooses representatives for the dense generating submodule, not for every
element of the closed correction space. -/
structure CanonicalMuGeneratorRepresentativeData
    (U : Set (Vec d)) (Y : canonicalMuBlockCorrectionGeneratorSubmodule U) where
  correction : CorrectionFieldData U
  toBlockL2_eq : correction.toBlockL2 = (Y : BlockL2 U)

/-- Choose a pointwise representative for a canonical dense-generator
correction. -/
noncomputable def canonicalMuGeneratorRepresentative
    (Y : canonicalMuBlockCorrectionGeneratorSubmodule U) :
    CanonicalMuGeneratorRepresentativeData U Y := by
  classical
  let f : Vec d → Vec d := Classical.choose Y.property
  let hf_tail := Classical.choose_spec Y.property
  let g : Vec d → Vec d := Classical.choose hf_tail
  let hg_tail := Classical.choose_spec hf_tail
  let hf : MemVectorL2 U f := Classical.choose hg_tail
  let hrest_f := Classical.choose_spec hg_tail
  let hg : MemVectorL2 U g := Classical.choose hrest_f
  let hrest := Classical.choose_spec hrest_f
  have hY : toBlockL2OfComponents hf hg = (Y : BlockL2 U) := hrest.1
  have hpot : IsPotentialZeroTraceOn U f := hrest.2.1
  have hsol : IsSolenoidalZeroNormalTraceOn U g := hrest.2.2
  refine
    { correction :=
        { potential := f
          flux := g
          potential_memL2 := hf
          flux_memL2 := hg
          isPotentialZeroTrace := hpot
          isSolenoidalZeroNormalTrace := hsol }
      toBlockL2_eq := ?_ }
  simpa [CorrectionFieldData.toBlockL2, CorrectionFieldData.toBlockField,
    toBlockL2OfComponents] using hY

/-- The chosen generator representative as correction-field data. -/
noncomputable def canonicalMuGeneratorCorrectionFieldData
    (Y : canonicalMuBlockCorrectionGeneratorSubmodule U) :
    CorrectionFieldData U :=
  (canonicalMuGeneratorRepresentative (U := U) Y).correction

theorem canonicalMuGeneratorCorrectionFieldData_toBlockL2
    (Y : canonicalMuBlockCorrectionGeneratorSubmodule U) :
    (canonicalMuGeneratorCorrectionFieldData (U := U) Y).toBlockL2 = (Y : BlockL2 U) :=
  (canonicalMuGeneratorRepresentative (U := U) Y).toBlockL2_eq

theorem canonicalMuCorrectionGeneratorEmbedding_eq_toHilbertBlockL2
    (Y : canonicalMuBlockCorrectionGeneratorSubmodule U) :
    (canonicalMuCorrectionGeneratorEmbedding U Y : HilbertBlockL2 U) =
      (canonicalMuGeneratorCorrectionFieldData (U := U) Y).toHilbertBlockL2 := by
  calc
    (canonicalMuCorrectionGeneratorEmbedding U Y : HilbertBlockL2 U)
        = blockL2ToHilbertBlockL2 (U := U) (Y : BlockL2 U) := rfl
    _ = blockL2ToHilbertBlockL2 (U := U)
          (canonicalMuGeneratorCorrectionFieldData (U := U) Y).toBlockL2 := by
          rw [canonicalMuGeneratorCorrectionFieldData_toBlockL2 (U := U) Y]
    _ = (canonicalMuGeneratorCorrectionFieldData (U := U) Y).toHilbertBlockL2 :=
          CorrectionFieldData.blockL2ToHilbertBlockL2_toBlockL2
            (canonicalMuGeneratorCorrectionFieldData (U := U) Y)

@[simp] theorem canonicalMuCorrectionGeneratorEmbedding_zero :
    canonicalMuCorrectionGeneratorEmbedding U
        (0 : canonicalMuBlockCorrectionGeneratorSubmodule U) = 0 := by
  apply Subtype.ext
  change blockL2ToHilbertBlockL2 (U := U) (0 : BlockL2 U) = 0
  simp

/-- The affine block state associated to a dense-generator correction. -/
noncomputable def canonicalMuGeneratorAffineField
    (P : BlockVec d) (Y : canonicalMuBlockCorrectionGeneratorSubmodule U) :
    BlockState d :=
  let Z := canonicalMuGeneratorCorrectionFieldData (U := U) Y
  { potential := fun x => P.1 + Z.potential x
    flux := fun x => P.2 + Z.flux x }

theorem canonicalMuGeneratorAffineField_admissible
    (P : BlockVec d) (Y : canonicalMuBlockCorrectionGeneratorSubmodule U) :
    IsBlockMuAdmissible U P (canonicalMuGeneratorAffineField (U := U) P Y) := by
  let Z := canonicalMuGeneratorCorrectionFieldData (U := U) Y
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [canonicalMuGeneratorAffineField, Z, sub_eq_add_neg, add_assoc, add_comm] using
      Z.potential_memL2
  · simpa [canonicalMuGeneratorAffineField, Z, sub_eq_add_neg, add_assoc, add_comm] using
      Z.isPotentialZeroTrace
  · simpa [canonicalMuGeneratorAffineField, Z, sub_eq_add_neg, add_assoc, add_comm] using
      Z.flux_memL2
  · simpa [canonicalMuGeneratorAffineField, Z, sub_eq_add_neg, add_assoc, add_comm] using
      Z.isSolenoidalZeroNormalTrace

theorem canonicalMuGeneratorAffineField_memBlockL2
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (P : BlockVec d) (Y : canonicalMuBlockCorrectionGeneratorSubmodule U) :
    MemBlockL2 U (canonicalMuGeneratorAffineField (U := U) P Y).eval :=
  (canonicalMuGeneratorAffineField_admissible (U := U) P Y).memBlockL2_eval

theorem canonicalMuGeneratorAffineField_correction_eq
    (P : BlockVec d) (Y : canonicalMuBlockCorrectionGeneratorSubmodule U) :
    ((canonicalMuGeneratorAffineField_admissible (U := U) P Y).toCorrectionFieldDataOfAdmissible).toHilbertBlockL2 =
      (canonicalMuGeneratorCorrectionFieldData (U := U) Y).toHilbertBlockL2 := by
  let Z := canonicalMuGeneratorCorrectionFieldData (U := U) Y
  change
    toHilbertBlockL2OfComponents
        (canonicalMuGeneratorAffineField_admissible (U := U) P Y).potentialCorrection_memL2
        (canonicalMuGeneratorAffineField_admissible (U := U) P Y).fluxCorrection_memL2 =
      Z.toHilbertBlockL2
  apply MeasureTheory.Lp.ext
  filter_upwards
      [coeFn_toHilbertBlockL2OfComponents (U := U)
        (f := fun x => (canonicalMuGeneratorAffineField (U := U) P Y).potential x - P.1)
        (g := fun x => (canonicalMuGeneratorAffineField (U := U) P Y).flux x - P.2)
        (canonicalMuGeneratorAffineField_admissible (U := U) P Y).potentialCorrection_memL2
        (canonicalMuGeneratorAffineField_admissible (U := U) P Y).fluxCorrection_memL2,
       (canonicalMuGeneratorCorrectionFieldData (U := U) Y).coeFn_toHilbertBlockL2]
    with x hleft hright
  rw [hleft, hright]
  apply HilbertBlockVec.ext
  · ext i
    simp [canonicalMuGeneratorAffineField, hilbertBlockField]
  · ext i
    simp [canonicalMuGeneratorAffineField, hilbertBlockField]

theorem canonicalMuGeneratorAffineField_hilbert_eq_const_add
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (P : BlockVec d) (Y : canonicalMuBlockCorrectionGeneratorSubmodule U) :
    toHilbertBlockL2OfBlockField (U := U)
        (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P Y) =
      blockVecToHilbertBlockL2Const (U := U) P +
        canonicalMuCorrectionGeneratorEmbedding U Y := by
  have hAdm := canonicalMuGeneratorAffineField_admissible (U := U) P Y
  calc
    toHilbertBlockL2OfBlockField (U := U)
        (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P Y)
        = blockVecToHilbertBlockL2Const (U := U) P +
            hAdm.toCorrectionFieldDataOfAdmissible.toHilbertBlockL2 := by
          exact hAdm.toHilbertBlockL2OfBlockField_eq_blockVecToHilbertBlockL2Const_add
    _ = blockVecToHilbertBlockL2Const (U := U) P +
          (canonicalMuGeneratorCorrectionFieldData (U := U) Y).toHilbertBlockL2 := by
          rw [canonicalMuGeneratorAffineField_correction_eq (U := U) P Y]
    _ = blockVecToHilbertBlockL2Const (U := U) P +
          canonicalMuCorrectionGeneratorEmbedding U Y := by
          rw [canonicalMuCorrectionGeneratorEmbedding_eq_toHilbertBlockL2 (U := U) Y]

theorem canonicalMuGeneratorAffineField_zero_hilbert_eq
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (Y : canonicalMuBlockCorrectionGeneratorSubmodule U) :
    toHilbertBlockL2OfBlockField (U := U)
        (canonicalMuGeneratorAffineField_memBlockL2 (U := U) (0 : BlockVec d) Y) =
      canonicalMuCorrectionGeneratorEmbedding U Y := by
  simpa using
    canonicalMuGeneratorAffineField_hilbert_eq_const_add
      (U := U) (P := (0 : BlockVec d)) Y

theorem canonicalMuGeneratorAffineField_zeroCorrection_hilbert_eq_const
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (P : BlockVec d) :
    toHilbertBlockL2OfBlockField (U := U)
        (canonicalMuGeneratorAffineField_memBlockL2
          (U := U) P (0 : canonicalMuBlockCorrectionGeneratorSubmodule U)) =
      blockVecToHilbertBlockL2Const (U := U) P := by
  simpa using
    canonicalMuGeneratorAffineField_hilbert_eq_const_add
      (U := U) (P := P) (0 : canonicalMuBlockCorrectionGeneratorSubmodule U)

theorem continuous_canonicalMuCorrectionGeneratorEmbedding (U : Set (Vec d)) :
    Continuous (canonicalMuCorrectionGeneratorEmbedding U) := by
  apply Continuous.subtype_mk
  exact (blockL2ToHilbertBlockL2 (U := U)).continuous.comp continuous_subtype_val

instance canonicalMuBlockCorrectionGeneratorSubmodule_separable (U : Set (Vec d)) :
    TopologicalSpace.SeparableSpace (canonicalMuBlockCorrectionGeneratorSubmodule U) := by
  let : Fact ((1 : ENNReal) ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  infer_instance

end CanonicalClosureGenerator
end

end Homogenization
