/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuOperator.HilbertOperator

/-! # Coeff Operator -/

namespace Homogenization

noncomputable section

/-!
# Mu operator -- coefficient-operator realization and system APIs

MuCoeffOperatorData structure and namespace with measurability,
uniform-bound, operator / operatorSymm / operatorCoercive constructors
under IsEllipticFieldOn, the blockPairing / blockEnergy integrability
lemmas, and the MuOperatorRealization / MuOperatorSystemData /
PotentialSolenoidalL2Data namespaces that feed into the Mu-recovery
layer.
-/

/--
Measurability and uniform boundedness package for the normalized doubled
coefficient operator attached to `a`.

This is the remaining analytic input needed to turn `x ↦ \mathbf A(a,x)` into a
concrete `MuOperatorRealization U a`.
-/
structure MuCoeffOperatorData {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) where
  /-- Measurability of the underlying domain. -/
  measurableSet_domain : MeasurableSet U
  /-- Measurability of the normalized pointwise coefficient operator. -/
  measurable_normalizedBlockCoeffOperator :
    Measurable (normalizedBlockCoeffOperator U a)
  /-- A uniform operator-norm bound. -/
  opNormBound : ℝ
  /-- Nonnegativity of the bound. -/
  opNormBound_nonneg : 0 ≤ opNormBound
  /-- The normalized coefficient operators are bounded by `opNormBound`. -/
  le_opNormBound :
    ∀ x : Vec d, ‖normalizedBlockCoeffOperator U a x‖ ≤ opNormBound

namespace MuCoeffOperatorData

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}

noncomputable def normalizedBlockCoeffOperatorNormBound
    (U : Set (Vec d)) (lam Lam : ℝ) : ℝ :=
  (MeasureTheory.volume U).toReal⁻¹ * Real.sqrt (blockMatrixOfCoeffNormSqBound lam Lam)

theorem normalizedBlockCoeffOperatorNormBound_nonneg
    (U : Set (Vec d)) (lam Lam : ℝ) :
    0 ≤ normalizedBlockCoeffOperatorNormBound (d := d) U lam Lam := by
  unfold normalizedBlockCoeffOperatorNormBound
  positivity

theorem normalizedBlockCoeffOperator_eq_of_mem (a : CoeffField d) {x : Vec d}
    (hx : x ∈ U) :
    normalizedBlockCoeffOperator U a x =
      (MeasureTheory.volume U).toReal⁻¹ •
        HilbertBlockVec.applyBlockMat (blockCoeffField a x) := by
  apply ContinuousLinearMap.ext
  intro X
  exact normalizedBlockCoeffOperator_apply_of_mem a hx X

@[simp] private theorem normalizedBlockCoeffOperator_eq_zero_of_not_mem (a : CoeffField d)
    {x : Vec d} (hx : x ∉ U) :
    normalizedBlockCoeffOperator U a x = 0 := by
  apply ContinuousLinearMap.ext
  intro X
  ext <;> simp [normalizedBlockCoeffOperator, blockCoeffField, restrictCoeffField, hx,
    HilbertBlockVec.applyBlockMat_apply, blockMatrixOfCoeff, blockMatVecMul, matVecMul,
    matTranspose, Matrix.inv_zero]

theorem measurable_normalizedBlockCoeffOperator_of_isEllipticFieldOn
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a) :
    Measurable (normalizedBlockCoeffOperator U a) := by
  classical
  have hrestrict : Measurable (fun x i j => restrictCoeffField U a x i j) := by
    refine measurable_pi_iff.2 ?_
    intro i
    refine measurable_pi_iff.2 ?_
    intro j
    convert (measurable_pi_iff.1 (measurable_pi_iff.1 hEll.1 i) j) using 1
    funext x
    by_cases hx : x ∈ U <;> simp [restrictCoeffField, hx]
  have hfull :
      Measurable (fun x α β =>
        toFullBlockMat (blockCoeffField (restrictCoeffField U a) x) α β) := by
    simpa [blockCoeffField] using
      measurable_toFullBlockMat_blockCoeffField (d := d) hrestrict
  have hop :
      Measurable (fun x =>
        fullEntriesToHilbertOperator d
          (toFullBlockMat (blockCoeffField (restrictCoeffField U a) x))) := by
    exact measurable_fullEntriesToHilbertOperator hfull
  simpa [normalizedBlockCoeffOperator, fullEntriesToHilbertOperator_toFullBlockMat] using!
    (measurable_const : Measurable (fun _ : Vec d => (MeasureTheory.volume U).toReal⁻¹)).smul hop

theorem le_normalizedBlockCoeffOperatorNormBound_of_isEllipticFieldOn
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a) (x : Vec d) :
    ‖normalizedBlockCoeffOperator U a x‖ ≤
      normalizedBlockCoeffOperatorNormBound (d := d) U lam Lam := by
  by_cases hx : x ∈ U
  · have hA :
        ‖HilbertBlockVec.applyBlockMat (blockCoeffField a x)‖ ≤
          Real.sqrt (blockMatrixOfCoeffNormSqBound lam Lam) := by
      apply HilbertBlockVec.opNorm_applyBlockMat_le_of_block_bound
      · exact Real.sqrt_nonneg _
      · intro X
        have hbound :=
          blockMatrixOfCoeff_image_bound_of_isEllipticMatrix (hEll.2 x hx) X
        calc
          blockVecDot (blockMatVecMul (blockCoeffField a x) X)
              (blockMatVecMul (blockCoeffField a x) X)
              ≤ blockMatrixOfCoeffNormSqBound lam Lam * blockVecDot X X := hbound
          _ = (Real.sqrt (blockMatrixOfCoeffNormSqBound lam Lam)) ^ 2 * blockVecDot X X := by
            rw [Real.sq_sqrt (blockMatrixOfCoeffNormSqBound_nonneg lam Lam)]
    rw [normalizedBlockCoeffOperator_eq_of_mem (U := U) a hx]
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
      _ = normalizedBlockCoeffOperatorNormBound (d := d) U lam Lam := by
          simp [normalizedBlockCoeffOperatorNormBound]
  · rw [normalizedBlockCoeffOperator_eq_zero_of_not_mem (U := U) a hx]
    rw [norm_zero]
    exact normalizedBlockCoeffOperatorNormBound_nonneg (d := d) U lam Lam

/-- Concrete measurable/bounded coefficient-operator data built directly from the
ellipticity assumptions recorded in `IsEllipticFieldOn`. -/
noncomputable def ofIsEllipticFieldOn {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) :
    MuCoeffOperatorData U a where
  measurableSet_domain := measurableSet_of_isEllipticFieldOn hEll
  measurable_normalizedBlockCoeffOperator :=
    measurable_normalizedBlockCoeffOperator_of_isEllipticFieldOn hEll
  opNormBound := normalizedBlockCoeffOperatorNormBound (d := d) U lam Lam
  opNormBound_nonneg := normalizedBlockCoeffOperatorNormBound_nonneg (d := d) U lam Lam
  le_opNormBound := le_normalizedBlockCoeffOperatorNormBound_of_isEllipticFieldOn hEll

/-- View the normalized coefficient operator as a uniformly bounded measurable
pointwise `L²` operator field. -/
noncomputable def toPointwiseField (M : MuCoeffOperatorData U a) :
    PointwiseHilbertBlockOperatorField U where
  field := normalizedBlockCoeffOperator U a
  measurable_field := M.measurable_normalizedBlockCoeffOperator
  opNormBound := M.opNormBound
  opNormBound_nonneg := M.opNormBound_nonneg
  le_opNormBound := M.le_opNormBound

/-- The bounded `L²` operator induced by the normalized coefficient field. -/
noncomputable def operator (M : MuCoeffOperatorData U a) :
    HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U :=
  M.toPointwiseField.toContinuousLinearMap

theorem ae_apply_operator (M : MuCoeffOperatorData U a)
    (F : HilbertBlockL2 U) :
    M.operator F =ᵐ[volumeMeasureOn U]
      fun x => normalizedBlockCoeffOperator U a x (F x) :=
  M.toPointwiseField.coeFn_toContinuousLinearMap F

theorem normalizedBlockCoeffOperator_inner_comm (x : Vec d)
    (X Y : HilbertBlockVec d) :
    inner ℝ (normalizedBlockCoeffOperator U a x X) Y =
      inner ℝ X (normalizedBlockCoeffOperator U a x Y) := by
  let B : BlockMat d := blockCoeffField (restrictCoeffField U a) x
  let c : ℝ := (MeasureTheory.volume U).toReal⁻¹
  have hcomm :
      blockVecDot Y.toBlockVec (blockMatVecMul B X.toBlockVec) =
        blockVecDot X.toBlockVec (blockMatVecMul B Y.toBlockVec) := by
    simpa [B, blockCoeffField] using!
      (blockVecDot_blockMatVecMul_blockMatrixOfCoeff_comm ((restrictCoeffField U a) x)
        Y.toBlockVec X.toBlockVec)
  have htoBlockX :
      ((c • HilbertBlockVec.ofBlockVec (blockMatVecMul B X.toBlockVec)).toBlockVec) =
        c • blockMatVecMul B X.toBlockVec := by
    ext i <;> simp [c, B, HilbertVec.toVec, mul_add]
  have htoBlockY :
      ((c • HilbertBlockVec.ofBlockVec (blockMatVecMul B Y.toBlockVec)).toBlockVec) =
        c • blockMatVecMul B Y.toBlockVec := by
    ext i <;> simp [c, B, HilbertVec.toVec, mul_add]
  rw [real_inner_comm, normalizedBlockCoeffOperator_apply, normalizedBlockCoeffOperator_apply,
    HilbertBlockVec.inner_def, HilbertBlockVec.inner_def,
    HilbertBlockVec.applyBlockMat_apply, HilbertBlockVec.applyBlockMat_apply,
    htoBlockX, htoBlockY, blockVecDot_smul_right, blockVecDot_smul_right]
  exact congrArg (fun t => c * t) hcomm

theorem normalizedBlockCoeffOperator_self_inner_lowerBound_of_mem
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a) {x : Vec d} (hx : x ∈ U)
    (X : HilbertBlockVec d) :
    ((MeasureTheory.volume U).toReal⁻¹ * (lam / (1 + 2 * Lam ^ 2))) * inner ℝ X X ≤
      inner ℝ (normalizedBlockCoeffOperator U a x X) X := by
  have hcoer :
      (lam / (1 + 2 * Lam ^ 2)) * blockVecDot X.toBlockVec X.toBlockVec ≤
        blockVecDot X.toBlockVec
          (blockMatVecMul (blockCoeffField a x) X.toBlockVec) := by
    simpa [blockCoeffField] using
      (blockMatrixOfCoeff_coercive_of_isEllipticMatrix (hEll.2 x hx) X.toBlockVec)
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

theorem nonempty_of_volume_toReal_pos
    (hvol : 0 < (MeasureTheory.volume U).toReal) : U.Nonempty := by
  by_contra hEmpty
  have hU : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hEmpty
  simp [hU] at hvol

theorem lam_pos_of_isEllipticFieldOn {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal) : 0 < lam := by
  rcases nonempty_of_volume_toReal_pos (U := U) hvol with ⟨x, hx⟩
  exact (hEll.2 x hx).1

theorem operatorSymm (M : MuCoeffOperatorData U a) :
    LinearMap.IsSymmetric (M.operator : HilbertBlockL2 U →ₗ[ℝ] HilbertBlockL2 U) := by
  intro F G
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [M.ae_apply_operator F, M.ae_apply_operator G, Filter.Eventually.of_forall
      (fun x => normalizedBlockCoeffOperator_inner_comm (U := U) (a := a) x (F x) (G x))]
    with x hF hG hsymm
  simpa [hF, hG] using hsymm

theorem operatorCoercive_of_isEllipticFieldOn (M : MuCoeffOperatorData U a)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal) :
    IsCoercive (energyBilinOfOperator M.operator) := by
  let C : ℝ :=
    (MeasureTheory.volume U).toReal⁻¹ * (lam / (1 + 2 * Lam ^ 2))
  refine ⟨C, ?_, ?_⟩
  · have hlam : 0 < lam := lam_pos_of_isEllipticFieldOn (U := U) (a := a) hEll hvol
    have hvolInv : 0 < (MeasureTheory.volume U).toReal⁻¹ := by
      positivity
    have hden : 0 < 1 + 2 * Lam ^ 2 := by
      nlinarith [sq_nonneg Lam]
    dsimp [C]
    exact mul_pos hvolInv (div_pos hlam hden)
  · intro F
    have hleftInt :
        MeasureTheory.Integrable (fun x =>
          C * inner ℝ (F x) (F x)) (volumeMeasureOn U) := by
      exact (MeasureTheory.L2.integrable_inner F F).const_mul C
    have hrightInt :
        MeasureTheory.Integrable (fun x =>
          inner ℝ ((M.operator F) x) (F x)) (volumeMeasureOn U) := by
      exact MeasureTheory.L2.integrable_inner (M.operator F) F
    have hmono :
        ∀ᵐ x ∂ volumeMeasureOn U,
          C * inner ℝ (F x) (F x) ≤
            inner ℝ ((M.operator F) x) (F x) := by
      filter_upwards
          [M.ae_apply_operator F,
           MeasureTheory.ae_restrict_of_forall_mem M.measurableSet_domain
             (fun x hx =>
               normalizedBlockCoeffOperator_self_inner_lowerBound_of_mem
                 (U := U) (a := a) hEll hx (F x))]
        with x hOp hpoint
      rw [hOp]
      simpa [C] using hpoint
    calc
      C * ‖F‖ * ‖F‖
        = ∫ x, C * inner ℝ (F x) (F x) ∂ volumeMeasureOn U := by
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
              C * ‖F‖ * ‖F‖ = C * (‖F‖ * ‖F‖) := by ring
              _ = C * ∫ x, inner ℝ (F x) (F x) ∂ volumeMeasureOn U := by rw [hnorm]
              _ = ∫ x, C * inner ℝ (F x) (F x) ∂ volumeMeasureOn U := by
                    rw [← MeasureTheory.integral_const_mul]
      _ ≤ ∫ x, inner ℝ ((M.operator F) x) (F x) ∂ volumeMeasureOn U := by
            exact MeasureTheory.integral_mono_ae hleftInt hrightInt hmono
      _ = energyBilinOfOperator M.operator F F := by
            rw [energyBilinOfOperator_apply, MeasureTheory.L2.inner_def]

end MuCoeffOperatorData

/--
The unnormalized pointwise doubled coefficient operator attached to `a`,
viewed as a bounded measurable operator field on the Hilbert block carrier.

This auxiliary field is used only to prove integrability of the raw pairing
`X · A(a,x) Y` from block `L²` control and ellipticity.
-/
noncomputable def rawBlockCoeffOperatorField {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a) :
    PointwiseHilbertBlockOperatorField U where
  field := fun x => HilbertBlockVec.applyBlockMat (blockCoeffField (restrictCoeffField U a) x)
  measurable_field := by
    have hrestrict : Measurable (fun x i j => restrictCoeffField U a x i j) := by
      refine measurable_pi_iff.2 ?_
      intro i
      refine measurable_pi_iff.2 ?_
      intro j
      convert (measurable_pi_iff.1 (measurable_pi_iff.1 hEll.1 i) j) using 1
      funext x
      by_cases hx : x ∈ U <;> simp [restrictCoeffField, hx]
    have hfull :
        Measurable (fun x α β =>
          toFullBlockMat (blockCoeffField (restrictCoeffField U a) x) α β) := by
      simpa [blockCoeffField] using
        measurable_toFullBlockMat_blockCoeffField (d := d) hrestrict
    have hop :
        Measurable (fun x =>
          fullEntriesToHilbertOperator d
            (toFullBlockMat (blockCoeffField (restrictCoeffField U a) x))) := by
      exact measurable_fullEntriesToHilbertOperator hfull
    simpa [fullEntriesToHilbertOperator_toFullBlockMat] using hop
  opNormBound := Real.sqrt (blockMatrixOfCoeffNormSqBound lam Lam)
  opNormBound_nonneg := Real.sqrt_nonneg _
  le_opNormBound := by
    intro x
    by_cases hx : x ∈ U
    · have hbound :
          ‖HilbertBlockVec.applyBlockMat (blockCoeffField a x)‖ ≤
            Real.sqrt (blockMatrixOfCoeffNormSqBound lam Lam) := by
        apply HilbertBlockVec.opNorm_applyBlockMat_le_of_block_bound
        · exact Real.sqrt_nonneg _
        · intro X
          have himage :=
            blockMatrixOfCoeff_image_bound_of_isEllipticMatrix (hEll.2 x hx) X
          calc
            blockVecDot (blockMatVecMul (blockCoeffField a x) X)
                (blockMatVecMul (blockCoeffField a x) X)
                ≤ blockMatrixOfCoeffNormSqBound lam Lam * blockVecDot X X := himage
            _ = (Real.sqrt (blockMatrixOfCoeffNormSqBound lam Lam)) ^ 2 * blockVecDot X X := by
                rw [Real.sq_sqrt (blockMatrixOfCoeffNormSqBound_nonneg lam Lam)]
      have hcoeff :
          blockCoeffField (restrictCoeffField U a) x = blockCoeffField a x := by
        simp [blockCoeffField, restrictCoeffField, hx]
      rw [hcoeff]
      exact hbound
    · have hzero :
          HilbertBlockVec.applyBlockMat (blockCoeffField (restrictCoeffField U a) x) = 0 := by
        apply ContinuousLinearMap.ext
        intro X
        ext i <;> simp [blockCoeffField, restrictCoeffField, hx,
          HilbertBlockVec.applyBlockMat_apply, blockMatrixOfCoeff, blockMatVecMul, matVecMul,
          matTranspose, Matrix.inv_zero]
      rw [hzero, norm_zero]
      exact Real.sqrt_nonneg _

/-- Ellipticity plus block `L²` control makes the raw doubled pairing
integrable on `U`. -/
theorem blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {lam Lam : ℝ} {X Y : BlockState d}
    (hX : MemBlockL2 U X.eval) (hY : MemBlockL2 U Y.eval)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    MeasureTheory.IntegrableOn (blockPairingIntegrand a X Y) U := by
  let M := rawBlockCoeffOperatorField (U := U) (a := a) hEll
  let FX : HilbertBlockL2 U := toHilbertBlockL2OfBlockField (U := U) hX
  let FY : HilbertBlockL2 U := toHilbertBlockL2OfBlockField (U := U) hY
  have hInner :
      MeasureTheory.Integrable
        (fun x => inner ℝ (FX x) ((M.toContinuousLinearMap FY) x))
        (volumeMeasureOn U) := by
    exact MeasureTheory.L2.integrable_inner FX (M.toContinuousLinearMap FY)
  have hAE :
      (fun x => inner ℝ (FX x) ((M.toContinuousLinearMap FY) x)) =ᵐ[volumeMeasureOn U]
        blockPairingIntegrand a X Y := by
    filter_upwards
        [M.coeFn_toContinuousLinearMap FY,
         coeFn_toHilbertBlockL2OfBlockField (U := U) (F := X.eval) hX,
         coeFn_toHilbertBlockL2OfBlockField (U := U) (F := Y.eval) hY,
         (MeasureTheory.ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hEll)).2
           (Filter.Eventually.of_forall fun x hx => hx)]
      with x hOp hXae hYae hx
    have hFX : FX x = hilbertifyBlockField X.eval x := by
      simpa [FX] using hXae
    have hFY : FY x = hilbertifyBlockField Y.eval x := by
      simpa [FY] using hYae
    rw [hFX, hOp]
    have hcoeff :
        blockCoeffField (restrictCoeffField U a) x = blockCoeffField a x := by
      simp [blockCoeffField, restrictCoeffField, hx]
    simp [M, rawBlockCoeffOperatorField, PointwiseHilbertBlockOperatorField.applyFn,
      blockPairingIntegrand, HilbertBlockVec.inner_def, hilbertifyBlockField, hcoeff, hFY]
  simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using hInner.congr hAE

/-- Ellipticity plus block `L²` control makes the raw doubled energy density
integrable on `U`. -/
theorem blockEnergyDensity_integrableOn_of_memBlockL2_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {lam Lam : ℝ} {X : BlockState d}
    (hX : MemBlockL2 U X.eval) (hEll : IsEllipticFieldOn lam Lam U a) :
    MeasureTheory.IntegrableOn (blockEnergyDensity a X) U := by
  have hPair :
      MeasureTheory.IntegrableOn (blockPairingIntegrand a X X) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      (U := U) (a := a) hX hX hEll
  rw [show blockEnergyDensity a X =
      fun x => (1 / 2 : ℝ) • blockPairingIntegrand a X X x by
        funext x
        simp [blockEnergyDensity, blockPairingIntegrand]]
  simpa [MeasureTheory.IntegrableOn] using! hPair.smul (1 / 2 : ℝ)

/--
Concrete `L²(U; \R^{2d})` data for the note's averaged doubled coefficient
operator.

The field `ae_apply` says that the operator acts pointwise by the doubled block
matrix `\mathbf A(a,x)`, multiplied by the normalizing factor appearing in
`\fint_U`.
-/
structure MuOperatorRealization {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) where
  /-- The ambient `L²` operator. -/
  operator : HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U
  /-- Almost-everywhere pointwise description of the averaged operator. -/
  ae_apply :
    ∀ F : HilbertBlockL2 U,
      operator F =ᵐ[volumeMeasureOn U]
        fun x =>
          (MeasureTheory.volume U).toReal⁻¹ •
            HilbertBlockVec.applyBlockMat (blockCoeffField a x) (F x)
  /-- Symmetry of the induced bilinear form. -/
  operatorSymm :
    LinearMap.IsSymmetric (operator : HilbertBlockL2 U →ₗ[ℝ] HilbertBlockL2 U)
  /-- Coercivity of the induced bilinear form. -/
  operatorCoercive : IsCoercive (energyBilinOfOperator operator)

namespace MuOperatorRealization

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}

/-- Forget the pointwise description and feed the operator package into the
Hilbert-space `\mu` problem. -/
noncomputable def toMuHilbertRealization
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (M : MuOperatorRealization U a)
    (correctionSpace : MuCorrectionSpaceData U) :
    MuHilbertRealization U a :=
  MuHilbertRealization.ofOperator correctionSpace
    M.operator M.operatorSymm M.operatorCoercive

/--
For typed block `L²` fields, the Hilbert-space bilinear form of a concrete
`MuOperatorRealization` reproduces the note's averaged doubled pairing.

The arguments appear in the order dictated by `energyBilinOfOperator`:
the operator acts on the first entry. Writing the theorem with the fields
swapped makes the right-hand side match the note's convention
`X \cdot \mathbf A(a,x) Y`.
-/
theorem energyBilin_eq_volumeAverage_swap_of_memBlockL2
    (M : MuOperatorRealization U a)
    {X Y : Vec d → BlockVec d} (hX : MemBlockL2 U X) (hY : MemBlockL2 U Y) :
    energyBilinOfOperator M.operator
      (toHilbertBlockL2OfBlockField (U := U) hY)
      (toHilbertBlockL2OfBlockField (U := U) hX) =
        volumeAverage U
          (fun x => blockVecDot (X x) (blockMatVecMul (blockCoeffField a x) (Y x))) := by
  rw [energyBilinOfOperator_apply, MeasureTheory.L2.inner_def]
  calc
    ∫ x, inner ℝ (M.operator (toHilbertBlockL2OfBlockField (U := U) hY) x)
        (toHilbertBlockL2OfBlockField (U := U) hX x) ∂ volumeMeasureOn U
      =
        ∫ x, (MeasureTheory.volume U).toReal⁻¹ *
          blockVecDot (X x) (blockMatVecMul (blockCoeffField a x) (Y x))
            ∂ volumeMeasureOn U := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards
                [M.ae_apply (toHilbertBlockL2OfBlockField (U := U) hY),
                 coeFn_toHilbertBlockL2OfBlockField (U := U) (F := X) hX,
                 coeFn_toHilbertBlockL2OfBlockField (U := U) (F := Y) hY]
              with x hOp hXae hYae
            let Z := blockMatVecMul (blockCoeffField a x) (Y x)
            rw [hOp, hXae, hYae]
            simp [hilbertifyBlockField, real_inner_comm,
              HilbertBlockVec.applyBlockMat_apply, HilbertBlockVec.inner_def]
            have htoBlock :
                (((MeasureTheory.volume U).toReal⁻¹ • HilbertBlockVec.ofBlockVec Z).toBlockVec) =
                  (MeasureTheory.volume U).toReal⁻¹ • Z := by
              ext i <;> simp [Z, HilbertVec.toVec]
            rw [htoBlock, blockVecDot_smul_right, mul_comm]
    _ =
        (MeasureTheory.volume U).toReal⁻¹ *
          ∫ x, blockVecDot (X x) (blockMatVecMul (blockCoeffField a x) (Y x))
            ∂ volumeMeasureOn U := by
            rw [MeasureTheory.integral_const_mul]
    _ =
        (MeasureTheory.volume U).toReal⁻¹ *
          ∫ x in U, blockVecDot (X x) (blockMatVecMul (blockCoeffField a x) (Y x))
            ∂ MeasureTheory.volume := by
            simp [volumeMeasureOn]
    _ = volumeAverage U
        (fun x => blockVecDot (X x) (blockMatVecMul (blockCoeffField a x) (Y x))) := by
          rfl

theorem energyBilin_eq_blockPairingAverage_of_blockState
    (M : MuOperatorRealization U a)
    {X Y : BlockState d} (hX : MemBlockL2 U X.eval) (hY : MemBlockL2 U Y.eval) :
    energyBilinOfOperator M.operator
      (toHilbertBlockL2OfBlockField (U := U) hY)
      (toHilbertBlockL2OfBlockField (U := U) hX) =
        blockPairingAverage U a X Y := by
  simpa [energyBilinOfOperator, blockPairingAverage, blockPairingIntegrand] using!
    M.energyBilin_eq_volumeAverage_swap_of_memBlockL2
      (X := X.eval) (Y := Y.eval) hX hY

theorem quadraticEnergy_eq_blockEnergyAverage_of_blockState
    (M : MuOperatorRealization U a)
    {X : BlockState d} (hX : MemBlockL2 U X.eval) :
    quadraticEnergy (energyBilinOfOperator M.operator)
      (toHilbertBlockL2OfBlockField (U := U) hX) =
        blockEnergyAverage U a X := by
  rw [quadraticEnergy, M.energyBilin_eq_blockPairingAverage_of_blockState hX hX]
  exact (blockEnergyAverage_eq_half_blockPairingAverage_self U a X).symm

end MuOperatorRealization

namespace MuCoeffOperatorData

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}

/-- Package measurable bounded coefficient-operator data together with the
symmetry and coercivity hypotheses needed by the doubled `\mu` problem. -/
noncomputable def toMuOperatorRealization
    (M : MuCoeffOperatorData U a)
    (operatorSymm :
      LinearMap.IsSymmetric (M.operator : HilbertBlockL2 U →ₗ[ℝ] HilbertBlockL2 U))
    (operatorCoercive : IsCoercive (energyBilinOfOperator M.operator)) :
    MuOperatorRealization U a where
  operator := M.operator
  ae_apply := by
    intro F
    filter_upwards
        [M.ae_apply_operator F,
         MeasureTheory.ae_restrict_of_forall_mem M.measurableSet_domain
           (fun x hx => normalizedBlockCoeffOperator_apply_of_mem a hx (F x))]
      with x hOp hEq
    rw [hOp, hEq]
  operatorSymm := operatorSymm
  operatorCoercive := operatorCoercive

/-- Package measurable bounded coefficient-operator data into a concrete doubled
operator realization using the symmetry and coercivity consequences of the
ellipticity hypotheses. -/
noncomputable def toMuOperatorRealizationOfIsEllipticFieldOn (M : MuCoeffOperatorData U a)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal) :
    MuOperatorRealization U a :=
  M.toMuOperatorRealization M.operatorSymm
    (M.operatorCoercive_of_isEllipticFieldOn hEll hvol)

end MuCoeffOperatorData

/--
Deterministic input data for the doubled `\mu` problem on `U`.

This bundles exactly the concrete operator-theoretic witnesses currently needed
to pass from a coefficient field to the Hilbert-space minimization engine. The
package is intentionally samplewise, so a future random-field layer can assign
one such package to each realization `\omega` without changing the deterministic
API.
-/
structure MuOperatorSystemData {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) where
  /-- The closed correction space `\Lpoto(U) × \Lsolo(U)`. -/
  correctionSpace : MuCorrectionSpaceData U
  /-- Measurable bounded coefficient-operator data. -/
  coeffOperatorData : MuCoeffOperatorData U a
  /-- Symmetry of the concrete doubled `L²` operator. -/
  operatorSymm :
    LinearMap.IsSymmetric
      (coeffOperatorData.operator : HilbertBlockL2 U →ₗ[ℝ] HilbertBlockL2 U)
  /-- Coercivity of the concrete doubled energy form. -/
  operatorCoercive :
    IsCoercive (energyBilinOfOperator coeffOperatorData.operator)

namespace MuOperatorSystemData

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}

/-- Replace the correction-space package while keeping the same coefficient
operator data, symmetry, and coercivity witnesses. -/
noncomputable def withCorrectionSpace (M : MuOperatorSystemData U a)
    (correctionSpace : MuCorrectionSpaceData U) :
    MuOperatorSystemData U a where
  correctionSpace := correctionSpace
  coeffOperatorData := M.coeffOperatorData
  operatorSymm := M.operatorSymm
  operatorCoercive := M.operatorCoercive

/-- The concrete doubled operator realization extracted from the deterministic
system package. -/
noncomputable def toMuOperatorRealization (M : MuOperatorSystemData U a) :
    MuOperatorRealization U a :=
  M.coeffOperatorData.toMuOperatorRealization M.operatorSymm M.operatorCoercive

/-- The concrete Hilbert-space realization of the doubled `\mu` problem
extracted from the deterministic system package. -/
noncomputable def toMuHilbertRealization
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (M : MuOperatorSystemData U a) :
    MuHilbertRealization U a :=
  (M.toMuOperatorRealization).toMuHilbertRealization M.correctionSpace

end MuOperatorSystemData

namespace PotentialSolenoidalL2Data

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}

/-- Build the deterministic doubled operator package directly from the packaged
block correction space `\Lpoto(U) × \Lsolo(U)` together with the concrete
coefficient-operator data. -/
noncomputable def toMuOperatorSystemData (M : PotentialSolenoidalL2Data U)
    (coeffOperatorData : MuCoeffOperatorData U a)
    (operatorSymm :
      LinearMap.IsSymmetric
        (coeffOperatorData.operator : HilbertBlockL2 U →ₗ[ℝ] HilbertBlockL2 U))
    (operatorCoercive :
      IsCoercive (energyBilinOfOperator coeffOperatorData.operator)) :
    MuOperatorSystemData U a where
  correctionSpace := M.toMuCorrectionSpaceData
  coeffOperatorData := coeffOperatorData
  operatorSymm := operatorSymm
  operatorCoercive := operatorCoercive

/-- Build the deterministic doubled operator system directly from a packaged
potential/solenoidal correction space and raw ellipticity assumptions. -/
noncomputable def toMuOperatorSystemDataOfIsEllipticFieldOn
    (M : PotentialSolenoidalL2Data U) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal) :
    MuOperatorSystemData U a := by
  let coeffOperatorData : MuCoeffOperatorData U a :=
    MuCoeffOperatorData.ofIsEllipticFieldOn (U := U) (a := a) hEll
  exact M.toMuOperatorSystemData coeffOperatorData
    coeffOperatorData.operatorSymm
    (coeffOperatorData.operatorCoercive_of_isEllipticFieldOn hEll hvol)

@[simp] theorem correctionSpace_toMuOperatorSystemData (M : PotentialSolenoidalL2Data U)
    (coeffOperatorData : MuCoeffOperatorData U a)
    (operatorSymm :
      LinearMap.IsSymmetric
        (coeffOperatorData.operator : HilbertBlockL2 U →ₗ[ℝ] HilbertBlockL2 U))
    (operatorCoercive :
      IsCoercive (energyBilinOfOperator coeffOperatorData.operator)) :
    (M.toMuOperatorSystemData coeffOperatorData operatorSymm operatorCoercive).correctionSpace =
      M.toMuCorrectionSpaceData :=
  rfl

end PotentialSolenoidalL2Data


end

end Homogenization
