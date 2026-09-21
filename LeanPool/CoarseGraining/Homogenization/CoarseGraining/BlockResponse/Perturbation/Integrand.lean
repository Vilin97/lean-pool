/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Foundations
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuAdmissibility

/-! # Integrand -/

namespace Homogenization

noncomputable section

/-!
# BlockResponse perturbation -- integrand algebra and plain upper bound

Integrand basics (zero / smul / add), the first-variation and variation-
energy integrands, the plainUpperBound upper bound under IsEllipticFieldOn,
and the resulting blockJValueSet / blockJ upper bounds.
-/

theorem blockResponse_integrand_zero {d : ℕ} (a : CoeffField d) (P Q : BlockVec d) :
    blockResponseIntegrand a P Q ({ potential := 0, flux := 0 } : BlockState d) = 0 := by
  funext x
  simp [blockResponseIntegrand, blockEnergyDensity, BlockState.eval, blockMatVecMul, blockVecDot,
    matVecMul_zero, vecDot_zero_right]

theorem blockResponse_integrand_smul {d : ℕ} (a : CoeffField d) (P Q : BlockVec d)
    (c : ℝ) (X : BlockState d) :
    blockResponseIntegrand a P Q (c • X) =
      fun x =>
        -(c ^ 2) * blockEnergyDensity a X x
          - c * blockVecDot P (blockMatVecMul (blockCoeffField a x) (X.eval x))
          + c * blockVecDot Q (X.eval x) := by
  funext x
  simp [blockResponseIntegrand, blockEnergyDensity, pow_two, blockMatVecMul_smul,
    blockVecDot_smul_left, blockVecDot_smul_right]
  ring

theorem blockResponse_integrand_smul_data_state {d : ℕ} (a : CoeffField d) (P Q : BlockVec d)
    (c : ℝ) (X : BlockState d) :
    blockResponseIntegrand a (c • P) (c • Q) (c • X) =
      fun x => c ^ 2 * blockResponseIntegrand a P Q X x := by
  rw [blockResponse_integrand_smul]
  funext x
  simp [blockResponseIntegrand, blockEnergyDensity, blockVecDot_smul_left]
  ring

/-- The linear term in the doubled response functional at base state `X`
in the direction `Y`. -/
noncomputable def blockFirstVariationIntegrand {d : ℕ} (a : CoeffField d) (P Q : BlockVec d)
    (X Y : BlockState d) : Vec d → ℝ :=
  fun x =>
    -blockVecDot P (blockMatVecMul (blockCoeffField a x) (Y.eval x))
      + blockVecDot Q (Y.eval x)
      - blockVecDot (Y.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x))

/-- The quadratic energy term governing the second variation of the doubled
response functional. -/
noncomputable def blockVariationEnergyIntegrand {d : ℕ} (a : CoeffField d)
    (Y : BlockState d) : Vec d → ℝ :=
  blockEnergyDensity a Y

@[simp] theorem blockVariationEnergyIntegrand_eq_blockEnergyDensity {d : ℕ}
    (a : CoeffField d) (Y : BlockState d) :
    blockVariationEnergyIntegrand a Y = blockEnergyDensity a Y :=
  rfl

theorem blockFirstVariationIntegrand_add_direction {d : ℕ} (a : CoeffField d)
    (P Q : BlockVec d) (X Y Z : BlockState d) :
    blockFirstVariationIntegrand a P Q X (Y + Z) =
      fun x =>
        blockFirstVariationIntegrand a P Q X Y x +
          blockFirstVariationIntegrand a P Q X Z x := by
  funext x
  simp [blockFirstVariationIntegrand, blockMatVecMul_add, blockVecDot_add_left,
    blockVecDot_add_right]
  ring

theorem blockFirstVariationIntegrand_smul_direction {d : ℕ} (a : CoeffField d)
    (P Q : BlockVec d) (X Y : BlockState d) (c : ℝ) :
    blockFirstVariationIntegrand a P Q X (c • Y) =
      fun x => c * blockFirstVariationIntegrand a P Q X Y x := by
  funext x
  simp [blockFirstVariationIntegrand, blockMatVecMul_smul, blockVecDot_smul_left,
    blockVecDot_smul_right]
  ring

theorem blockResponse_integrand_add_smul_eq_firstVariation_sub_energy {d : ℕ}
    (a : CoeffField d) (P Q : BlockVec d) (X Y : BlockState d) (c : ℝ) :
    blockResponseIntegrand a P Q (X + c • Y) =
      fun x =>
        blockResponseIntegrand a P Q X x +
          c * blockFirstVariationIntegrand a P Q X Y x -
          c ^ 2 * blockVariationEnergyIntegrand a Y x := by
  funext x
  have hcomm :
      blockVecDot (X.eval x) (blockMatVecMul (blockCoeffField a x) (Y.eval x)) =
        blockVecDot (Y.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x)) := by
    simpa [blockCoeffField] using
      (blockVecDot_blockMatVecMul_blockMatrixOfCoeff_comm
        (A := a x) (X := X.eval x) (Y := Y.eval x))
  simp [blockResponseIntegrand, blockFirstVariationIntegrand, blockVariationEnergyIntegrand,
    blockEnergyDensity, blockMatVecMul_add, blockMatVecMul_smul, blockVecDot_add_left,
    blockVecDot_add_right, blockVecDot_smul_left, blockVecDot_smul_right, pow_two]
  rw [hcomm]
  ring

theorem blockResponse_integrand_add_eq_firstVariation_sub_energy {d : ℕ}
    (a : CoeffField d) (P Q : BlockVec d) (X Y : BlockState d) :
    blockResponseIntegrand a P Q (X + Y) =
      fun x =>
        blockResponseIntegrand a P Q X x +
          blockFirstVariationIntegrand a P Q X Y x -
          blockVariationEnergyIntegrand a Y x := by
  funext x
  have hcomm :
      blockVecDot (X.eval x) (blockMatVecMul (blockCoeffField a x) (Y.eval x)) =
        blockVecDot (Y.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x)) := by
    simpa [blockCoeffField] using
      (blockVecDot_blockMatVecMul_blockMatrixOfCoeff_comm
        (A := a x) (X := X.eval x) (Y := Y.eval x))
  simp [blockResponseIntegrand, blockFirstVariationIntegrand, blockVariationEnergyIntegrand,
    blockEnergyDensity, blockMatVecMul_add, blockVecDot_add_left, blockVecDot_add_right]
  rw [hcomm]
  ring

theorem volumeAverage_blockResponse_integrand_add_smul_eq_firstVariation_sub_energy
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) (P Q : BlockVec d)
    (X Y : BlockState d) (c : ℝ)
    (hresp : MeasureTheory.IntegrableOn (blockResponseIntegrand a P Q X) U)
    (hlin : MeasureTheory.IntegrableOn (blockFirstVariationIntegrand a P Q X Y) U)
    (henergy : MeasureTheory.IntegrableOn (blockVariationEnergyIntegrand a Y) U) :
    volumeAverage U (blockResponseIntegrand a P Q (X + c • Y)) =
      volumeAverage U (blockResponseIntegrand a P Q X) +
        c * volumeAverage U (blockFirstVariationIntegrand a P Q X Y) -
        c ^ 2 * volumeAverage U (blockVariationEnergyIntegrand a Y) := by
  rw [blockResponse_integrand_add_smul_eq_firstVariation_sub_energy]
  have hlin_smul : MeasureTheory.IntegrableOn (c • blockFirstVariationIntegrand a P Q X Y) U := by
    simpa [MeasureTheory.IntegrableOn] using hlin.integrable.smul c
  have henergy_smul :
      MeasureTheory.IntegrableOn ((c ^ 2) • blockVariationEnergyIntegrand a Y) U := by
    simpa [MeasureTheory.IntegrableOn] using henergy.integrable.smul (c ^ 2)
  have hadd :
      MeasureTheory.IntegrableOn
        (blockResponseIntegrand a P Q X + c • blockFirstVariationIntegrand a P Q X Y) U := by
    simpa [MeasureTheory.IntegrableOn] using hresp.integrable.add hlin_smul.integrable
  have hfun :
      (fun x =>
        blockResponseIntegrand a P Q X x +
          c * blockFirstVariationIntegrand a P Q X Y x -
          c ^ 2 * blockVariationEnergyIntegrand a Y x) =
        (blockResponseIntegrand a P Q X + c • blockFirstVariationIntegrand a P Q X Y) -
          (c ^ 2) • blockVariationEnergyIntegrand a Y := by
    funext x
    simp [sub_eq_add_neg, smul_eq_mul]
  rw [hfun]
  rw [volumeAverage_sub hadd henergy_smul, volumeAverage_add hresp hlin_smul, volumeAverage_smul,
    volumeAverage_smul]

theorem volumeAverage_blockResponse_integrand_add_eq_firstVariation_sub_energy
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) (P Q : BlockVec d)
    (X Y : BlockState d)
    (hresp : MeasureTheory.IntegrableOn (blockResponseIntegrand a P Q X) U)
    (hlin : MeasureTheory.IntegrableOn (blockFirstVariationIntegrand a P Q X Y) U)
    (henergy : MeasureTheory.IntegrableOn (blockVariationEnergyIntegrand a Y) U) :
    volumeAverage U (blockResponseIntegrand a P Q (X + Y)) =
      volumeAverage U (blockResponseIntegrand a P Q X) +
        volumeAverage U (blockFirstVariationIntegrand a P Q X Y) -
        volumeAverage U (blockVariationEnergyIntegrand a Y) := by
  rw [blockResponse_integrand_add_eq_firstVariation_sub_energy]
  have hadd :
      MeasureTheory.IntegrableOn
        (blockResponseIntegrand a P Q X + blockFirstVariationIntegrand a P Q X Y) U := by
    simpa [MeasureTheory.IntegrableOn] using hresp.integrable.add hlin.integrable
  have hfun :
      (fun x =>
        blockResponseIntegrand a P Q X x +
          blockFirstVariationIntegrand a P Q X Y x -
          blockVariationEnergyIntegrand a Y x) =
        (blockResponseIntegrand a P Q X + blockFirstVariationIntegrand a P Q X Y) -
          blockVariationEnergyIntegrand a Y := by
    funext x
    simp [sub_eq_add_neg]
  rw [hfun]
  rw [volumeAverage_sub hadd henergy, volumeAverage_add hresp hlin]

theorem volumeAverage_blockFirstVariationIntegrand_zero_data_eq_zero_of_mem_responseSpace
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {X Y : BlockState d}
    (hX : BlockResponseSpace a U X) (hY : IsBlockTestOn U Y) :
    volumeAverage U (blockFirstVariationIntegrand a 0 0 X Y) = 0 := by
  apply volumeAverage_eq_zero_of_integral_eq_zero
  have horth := hX.2.2 Y hY
  have hfun :
      blockFirstVariationIntegrand a (0 : BlockVec d) 0 X Y =
        fun x =>
          -blockVecDot (Y.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x)) := by
    funext x
    simp [blockFirstVariationIntegrand, blockVecDot, vecDot_zero_left]
  rw [hfun]
  rw [MeasureTheory.integral_neg]
  simpa using horth

noncomputable def blockResponsePlainUpperBound {d : ℕ} (lam Lam : ℝ)
    (P Q : BlockVec d) : ℝ :=
  (lam / (1 + 2 * Lam ^ 2))⁻¹ * blockVecDot Q Q +
    (lam / (1 + 2 * Lam ^ 2))⁻¹ *
      blockMatrixOfCoeffNormSqBound lam Lam * blockVecDot P P

theorem blockResponseIntegrand_le_plainUpperBound_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (P Q : BlockVec d) (X : BlockState d) :
    ∀ x ∈ U,
      blockResponseIntegrand a P Q X x ≤ blockResponsePlainUpperBound lam Lam P Q := by
  intro x hx
  let B : BlockMat d := blockCoeffField a x
  let Z : BlockVec d := X.eval x
  let R : BlockVec d := Q - blockMatVecMul B P
  let c : ℝ := lam / (1 + 2 * Lam ^ 2)
  have hA : IsEllipticMatrix lam Lam (a x) := hEll.2 x hx
  have hc_pos : 0 < c := by
    have hden_pos : 0 < 1 + 2 * Lam ^ 2 := by
      nlinarith [sq_nonneg Lam]
    exact div_pos hA.1 hden_pos
  have hcoercive :
      c * blockVecDot Z Z ≤ blockVecDot Z (blockMatVecMul B Z) := by
    simpa [c, B, Z, blockCoeffField] using
      blockMatrixOfCoeff_coercive_of_isEllipticMatrix hA Z
  have himageP :
      blockVecDot (blockMatVecMul B P) (blockMatVecMul B P) ≤
        blockMatrixOfCoeffNormSqBound lam Lam * blockVecDot P P := by
    simpa [B, blockCoeffField] using
      blockMatrixOfCoeff_image_bound_of_isEllipticMatrix hA P
  have hrewrite :
      blockResponseIntegrand a P Q X x =
        -((1 / 2 : ℝ) * blockVecDot Z (blockMatVecMul B Z)) + blockVecDot R Z := by
    have hcomm :
        blockVecDot P (blockMatVecMul B Z) = blockVecDot Z (blockMatVecMul B P) := by
      simpa [B, blockCoeffField] using
        blockVecDot_blockMatVecMul_blockMatrixOfCoeff_comm (a x) P Z
    have hsub :
        blockVecDot (X.eval x) (Q - blockMatVecMul (blockCoeffField a x) P) =
          blockVecDot (X.eval x) Q -
            blockVecDot (X.eval x) (blockMatVecMul (blockCoeffField a x) P) := by
      have hsubVec :
          Q - blockMatVecMul (blockCoeffField a x) P =
            Q + (-1 : ℝ) • blockMatVecMul (blockCoeffField a x) P := by
        ext i <;> simp [sub_eq_add_neg]
      rw [hsubVec]
      rw [blockVecDot_add_right, blockVecDot_smul_right]
      ring
    unfold blockResponseIntegrand blockEnergyDensity
    dsimp [Z, B, R]
    rw [hcomm, blockVecDot_comm Q (X.eval x)]
    rw [show blockVecDot (Q - blockMatVecMul (blockCoeffField a x) P) (X.eval x) =
        blockVecDot (X.eval x) (Q - blockMatVecMul (blockCoeffField a x) P) by
          rw [blockVecDot_comm]]
    rw [hsub]
    ring
  have hCS :
      blockVecDot R Z ^ 2 ≤ blockVecDot R R * blockVecDot Z Z :=
    sq_blockVecDot_le_blockVecDot_mul_blockVecDot R Z
  have hR_nonneg : 0 ≤ blockVecDot R R := blockVecDot_nonneg R
  have hZ_nonneg : 0 ≤ blockVecDot Z Z := blockVecDot_nonneg Z
  have hYoungAbs :
      |blockVecDot R Z| ≤
        (1 / (2 * c)) * blockVecDot R R + (c / 2) * blockVecDot Z Z := by
    have hA_nonneg :
        0 ≤ (1 / (2 * c)) * blockVecDot R R + (c / 2) * blockVecDot Z Z := by
      positivity
    have hA_sq :
        blockVecDot R R * blockVecDot Z Z ≤
          ((1 / (2 * c)) * blockVecDot R R + (c / 2) * blockVecDot Z Z) ^ 2 := by
      let r : ℝ := blockVecDot R R
      let z : ℝ := blockVecDot Z Z
      have hcoeff_nonneg : 0 ≤ (1 / (4 * c ^ 2) : ℝ) := by
        positivity
      have hsq_nonneg :
          0 ≤ (r - c ^ 2 * z) ^ 2 := by
        positivity
      have hidentity :
          ((1 / (2 * c)) * r + (c / 2) * z) ^ 2 - r * z =
            (1 / (4 * c ^ 2)) * (r - c ^ 2 * z) ^ 2 := by
        field_simp [hc_pos.ne']
        ring
      have hmain :
          r * z ≤ ((1 / (2 * c)) * r + (c / 2) * z) ^ 2 := by
        nlinarith [hidentity, hsq_nonneg, hcoeff_nonneg]
      simpa [r, z] using hmain
    have hAbs_sq :
        |blockVecDot R Z| ^ 2 ≤
          ((1 / (2 * c)) * blockVecDot R R + (c / 2) * blockVecDot Z Z) ^ 2 := by
      calc
        |blockVecDot R Z| ^ 2 = blockVecDot R Z ^ 2 := by
          rw [sq_abs]
        _ ≤ blockVecDot R R * blockVecDot Z Z := hCS
        _ ≤ ((1 / (2 * c)) * blockVecDot R R + (c / 2) * blockVecDot Z Z) ^ 2 := hA_sq
    exact le_of_sq_le_sq hAbs_sq hA_nonneg
  have hYoung :
      blockVecDot R Z ≤
        (1 / (2 * c)) * blockVecDot R R + (c / 2) * blockVecDot Z Z := by
    exact le_trans (le_abs_self _) hYoungAbs
  have hmain :
      blockResponseIntegrand a P Q X x ≤ (1 / (2 * c)) * blockVecDot R R := by
    rw [hrewrite]
    nlinarith [hYoung, hcoercive]
  have hR_bound :
      blockVecDot R R ≤
        2 * (blockVecDot Q Q + blockVecDot (blockMatVecMul B P) (blockMatVecMul B P)) := by
    simpa [R] using blockVecDot_sub_self_le Q (blockMatVecMul B P)
  have hhalf_nonneg : 0 ≤ 1 / (2 * c) := by
    positivity
  have hsplit :
      (1 / (2 * c)) *
          (2 * (blockVecDot Q Q + blockVecDot (blockMatVecMul B P) (blockMatVecMul B P))) =
        c⁻¹ * blockVecDot Q Q +
          c⁻¹ * blockVecDot (blockMatVecMul B P) (blockMatVecMul B P) := by
    field_simp [hc_pos.ne']
  have hcInv_nonneg : 0 ≤ c⁻¹ := by
    positivity
  calc
    blockResponseIntegrand a P Q X x ≤ (1 / (2 * c)) * blockVecDot R R := hmain
    _ ≤ (1 / (2 * c)) *
          (2 * (blockVecDot Q Q + blockVecDot (blockMatVecMul B P) (blockMatVecMul B P))) := by
        gcongr
    _ = c⁻¹ * blockVecDot Q Q +
          c⁻¹ * blockVecDot (blockMatVecMul B P) (blockMatVecMul B P) := hsplit
    _ ≤ c⁻¹ * blockVecDot Q Q +
          c⁻¹ * (blockMatrixOfCoeffNormSqBound lam Lam * blockVecDot P P) := by
        gcongr
    _ = blockResponsePlainUpperBound lam Lam P Q := by
        simp [blockResponsePlainUpperBound, c, mul_assoc, mul_left_comm, mul_comm]

theorem volumeAverage_blockResponseIntegrand_le_plainUpperBound_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hEll : IsEllipticFieldOn lam Lam U a)
    (P Q : BlockVec d) (X : BlockState d)
    (hInt : MeasureTheory.IntegrableOn (blockResponseIntegrand a P Q X) U)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0) :
    volumeAverage U (blockResponseIntegrand a P Q X) ≤
      blockResponsePlainUpperBound lam Lam P Q := by
  apply volumeAverage_le_of_le_on hU hInt hvol
  exact blockResponseIntegrand_le_plainUpperBound_of_isEllipticFieldOn hEll P Q X

theorem blockJValueSet_bddAbove_of_isEllipticFieldOn_of_integrableOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (P Q : BlockVec d)
    (hInt :
      ∀ X : BlockState d, BlockResponseSpace a U X →
        MeasureTheory.IntegrableOn (blockResponseIntegrand a P Q X) U) :
    BddAbove (blockJValueSet U P Q a) := by
  refine ⟨blockResponsePlainUpperBound lam Lam P Q, ?_⟩
  rintro m ⟨X, hX, _, rfl⟩
  exact volumeAverage_blockResponseIntegrand_le_plainUpperBound_of_isEllipticFieldOn
    hU hEll P Q X (hInt X hX) hvol

theorem le_blockJ_of_mem_blockJValueSet_of_isEllipticFieldOn_of_integrableOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (P Q : BlockVec d)
    (hInt :
      ∀ X : BlockState d, BlockResponseSpace a U X →
        MeasureTheory.IntegrableOn (blockResponseIntegrand a P Q X) U)
    {m : ℝ} (hm : m ∈ blockJValueSet U P Q a) :
    m ≤ BlockJ U P Q a := by
  unfold BlockJ
  exact
    le_csSup
      (blockJValueSet_bddAbove_of_isEllipticFieldOn_of_integrableOn hU hEll hvol P Q hInt)
      hm

theorem blockJValueSet_bddAbove_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (P Q : BlockVec d) :
    BddAbove (blockJValueSet U P Q a) := by
  refine ⟨blockResponsePlainUpperBound lam Lam P Q, ?_⟩
  rintro m ⟨X, hX, hIntX, rfl⟩
  exact volumeAverage_blockResponseIntegrand_le_plainUpperBound_of_isEllipticFieldOn
    hU hEll P Q X
    (blockResponseIntegrand_integrableOn_of_mem_responseSpace_of_integrabilityData_of_isEllipticFieldOn
      hX hIntX hEll P Q)
    hvol

theorem le_blockJ_of_mem_blockJValueSet_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (P Q : BlockVec d) {m : ℝ} (hm : m ∈ blockJValueSet U P Q a) :
    m ≤ BlockJ U P Q a := by
  unfold BlockJ
  exact le_csSup (blockJValueSet_bddAbove_of_isEllipticFieldOn hU hEll hvol P Q) hm

theorem blockJ_le_plainUpperBound_of_isEllipticFieldOn_of_integrableOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (P Q : BlockVec d)
    (hInt :
      ∀ X : BlockState d, BlockResponseSpace a U X →
        MeasureTheory.IntegrableOn (blockResponseIntegrand a P Q X) U) :
    BlockJ U P Q a ≤ blockResponsePlainUpperBound lam Lam P Q := by
  unfold BlockJ
  refine csSup_le ?_ ?_
  refine ⟨0, ?_⟩
  have hZeroInt :
      BlockResponseIntegrabilityData U a ({ potential := 0, flux := 0 } : BlockState d) :=
    blockResponseIntegrabilityData_of_flux_memL2_of_mem_responseSpace_of_isEllipticFieldOn
      (blockResponse_zero_mem_responseSpace a U)
      (by
        change MemVectorL2 U (0 : Vec d → Vec d)
        exact MeasureTheory.MemLp.zero)
      hEll
  refine ⟨({ potential := 0, flux := 0 } : BlockState d),
    blockResponse_zero_mem_responseSpace a U, hZeroInt, ?_⟩
  rw [blockResponse_integrand_zero]
  simp [volumeAverage]
  rintro m ⟨X, hX, _, rfl⟩
  exact volumeAverage_blockResponseIntegrand_le_plainUpperBound_of_isEllipticFieldOn
    hU hEll P Q X (hInt X hX) hvol

theorem blockJ_le_plainUpperBound_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (P Q : BlockVec d) :
    BlockJ U P Q a ≤ blockResponsePlainUpperBound lam Lam P Q := by
  unfold BlockJ
  refine csSup_le ?_ ?_
  · refine ⟨0, ?_⟩
    refine ⟨({ potential := 0, flux := 0 } : BlockState d),
      blockResponse_zero_mem_responseSpace a U, blockResponseIntegrabilityData_zero U a, ?_⟩
    rw [blockResponse_integrand_zero]
    simp [volumeAverage]
  · rintro m ⟨X, hX, hIntX, rfl⟩
    exact volumeAverage_blockResponseIntegrand_le_plainUpperBound_of_isEllipticFieldOn
      hU hEll P Q X
      (blockResponseIntegrand_integrableOn_of_mem_responseSpace_of_integrabilityData_of_isEllipticFieldOn
        hX hIntX hEll P Q)
      hvol

end

end Homogenization
