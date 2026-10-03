/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Definitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.AnnealedSubadditivity
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAverageMoments.Theory
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.Scalarization

/-! # Scalar Algebra -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section52

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section
/-!
# Section 5.2 internals: ScalarAlgebra

Scalar identities, positive-excess algebra, and product estimates.
-/

/-- The `1 <= Theta_n` part of the scalar preliminary lemma, with the
inverse-star positivity proved in Chapter 4. -/
theorem one_le_thetaAtScale_of_integrable_coarseFullBlockMatrixAtCube
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (n : ℤ)
    (hBlock : Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d n)) P) :
    1 ≤ thetaAtScale hP hStruct n := by
  simpa [thetaAtScale, Ch04.Internal.thetaAtScale_eq_scalarization_contrast] using
    Ch04.RestrictionLawCarrier.Internal.one_le_scalar_contrast_of_primitive_of_integrable_coarseFullBlockMatrixAtCube hP
      (Ch04.Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct)
      (Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct n)
      hBlock

/-- The `Theta_n <= widetildeTheta_n` part of the scalar preliminary lemma,
using the direct Chapter 4 moment-factor endpoint. -/
theorem thetaAtScale_le_widetildeThetaAtScale_of_integrable_factor_observables
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (hBlock :
      ∀ l : ℕ,
        Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (l : ℤ))) P)
    (hUpperPowInt :
      ∀ l : ℕ,
        Integrable
          (fun a : RegCoeffField d =>
            (Ch04.LambdaSqCoeffField (originCube d (l : ℤ)) hP4.sUpper (.finite 1) a) ^
              hP4.xi) P)
    (hLowerPowInt :
      ∀ l : ℕ,
        Integrable
          (fun a : RegCoeffField d =>
            ((Ch04.lambdaSqCoeffField (originCube d (l : ℤ)) hP4.sLower (.finite 1) a)⁻¹) ^
              hP4.xi) P)
    (n : ℕ) :
    thetaAtScale hP hStruct (n : ℤ) ≤
      widetildeThetaAtScale P (n : ℤ) hP4 := by
  simpa [thetaAtScale, widetildeThetaAtScale] using
    hP.thetaAtScale_le_widetildeThetaAtScale_of_integrable_factor_observables
      hStruct hP4.sUpper_pos hP4.sLower_pos (Nat.succ_le_of_lt hP4.xi_pos)
      hBlock
      (fun l => hP.aemeasurable_LambdaSqCoeffField_finite_one
        (originCube d (l : ℤ)) hP4.sUpper_pos)
      (fun l => hP.aemeasurable_lambdaSqCoeffField_finite_one_inv
        (originCube d (l : ℤ)) hP4.sLower_pos)
      hUpperPowInt hLowerPowInt n

/-- The upper positive-excess moment is nonnegative. -/
theorem LambdaPositiveExcessMomentAtScale_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (s : ℝ) (ξ : ℕ)
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ) :
    0 ≤ LambdaPositiveExcessMomentAtScale P m s ξ hP hStruct := by
  simpa [LambdaPositiveExcessMomentAtScale] using
    Ch04.annealedMomentRoot_nonneg_of_nonneg P ξ
      (fun a : RegCoeffField d =>
        le_max_right
          (Ch04.LambdaSqCoeffField (originCube d m) s (.finite 1) a -
            hP.barSigmaAtScale hStruct 0)
          0)

/-- The lower inverse positive-excess moment is nonnegative. -/
theorem lambdaInvPositiveExcessMomentAtScale_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (s : ℝ) (ξ : ℕ)
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ) :
    0 ≤ lambdaInvPositiveExcessMomentAtScale P m s ξ hP hStruct := by
  simpa [lambdaInvPositiveExcessMomentAtScale] using
    Ch04.annealedMomentRoot_nonneg_of_nonneg P ξ
      (fun a : RegCoeffField d =>
        le_max_right
          ((Ch04.lambdaSqCoeffField (originCube d m) s (.finite 1) a)⁻¹ -
            (hP.barSigmaStarAtScale hStruct 0)⁻¹)
          0)

theorem real_le_base_add_max_sub_base_zero (x base : ℝ) :
    x ≤ base + max (x - base) 0 := by
  have h : x - base ≤ max (x - base) 0 := le_max_left _ _
  linarith

theorem max_sub_base_zero_le_of_le_base_add_nonneg
    {x base y : ℝ} (hy : 0 ≤ y) (hxy : x ≤ base + y) :
    max (x - base) 0 ≤ y := by
  have hsub : x - base ≤ y := by linarith
  exact max_le hsub hy

theorem weighted_sum_le_base_add_weighted_positiveExcess
    {ι : Type*} {s : Finset ι} {w f : ι → ℝ} {base : ℝ}
    (hbase : 0 ≤ base)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i ≤ 1) :
    (∑ i ∈ s, w i * f i) ≤
      base + ∑ i ∈ s, w i * max (f i - base) 0 := by
  have hterm :
      ∀ i ∈ s, w i * f i ≤ w i * (base + max (f i - base) 0) := by
    intro i hi
    exact mul_le_mul_of_nonneg_left
      (real_le_base_add_max_sub_base_zero (f i) base) (hw_nonneg i hi)
  have hsum_term :
      (∑ i ∈ s, w i * f i) ≤
        ∑ i ∈ s, w i * (base + max (f i - base) 0) :=
    Finset.sum_le_sum hterm
  have hweight_base :
      base * (∑ i ∈ s, w i) ≤ base := by
    calc
      base * (∑ i ∈ s, w i) ≤ base * 1 :=
        mul_le_mul_of_nonneg_left hw_sum hbase
      _ = base := by ring
  calc
    (∑ i ∈ s, w i * f i)
        ≤ ∑ i ∈ s, w i * (base + max (f i - base) 0) := hsum_term
    _ = ∑ i ∈ s, (w i * base + w i * max (f i - base) 0) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        ring
    _ = base * (∑ i ∈ s, w i) +
          ∑ i ∈ s, w i * max (f i - base) 0 := by
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [← Finset.sum_mul]
          ring
    _ ≤ base + ∑ i ∈ s, w i * max (f i - base) 0 := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right hweight_base
            (∑ i ∈ s, w i * max (f i - base) 0)

theorem max_sup'_sub_base_le_sup'_max_sub_base
    {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) (base : ℝ) :
    max (s.sup' hs f - base) 0 ≤
      s.sup' hs (fun i => max (f i - base) 0) := by
  have hsup_nonneg :
      0 ≤ s.sup' hs (fun i => max (f i - base) 0) := by
    rcases hs with ⟨i0, hi0⟩
    exact (le_max_right (f i0 - base) 0).trans
      (Finset.le_sup' (f := fun i => max (f i - base) 0) hi0)
  refine max_le ?_ hsup_nonneg
  have hle :
      s.sup' hs f ≤ base + s.sup' hs (fun i => max (f i - base) 0) := by
    refine Finset.sup'_le hs f ?_
    intro i hi
    have hi_le :
        max (f i - base) 0 ≤
          s.sup' hs (fun i => max (f i - base) 0) :=
      Finset.le_sup' (f := fun i => max (f i - base) 0) hi
    have hfi : f i ≤ base + max (f i - base) 0 :=
      real_le_base_add_max_sub_base_zero (f i) base
    linarith
  linarith

theorem section52_sq_finset_sum_weighted_rpow_half_le_finset_sum_weighted
    {ι : Type*} (s : Finset ι) {w H : ι → ℝ}
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hH_nonneg : ∀ i, 0 ≤ H i)
    (hw_sum : ∑ i ∈ s, w i ≤ 1) :
    (∑ i ∈ s, w i * Real.rpow (H i) (1 / 2 : ℝ)) ^ 2 ≤
      ∑ i ∈ s, w i * H i := by
  classical
  let sqrtH : ι → ℝ := fun i => Real.rpow (H i) (1 / 2 : ℝ)
  let W : ℝ := ∑ i ∈ s, w i
  let B : ℝ := ∑ i ∈ s, w i * H i
  have hW_nonneg : 0 ≤ W := by
    dsimp [W]
    exact Finset.sum_nonneg fun i _hi => hw_nonneg i
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg fun i _hi => mul_nonneg (hw_nonneg i) (hH_nonneg i)
  have hholder :
      ∑ i ∈ s, w i * sqrtH i ≤
        W ^ (1 - (2 : ℝ)⁻¹) *
          (∑ i ∈ s, w i * sqrtH i ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ := by
    simpa [W, sqrtH] using
      Real.inner_le_weight_mul_Lp_of_nonneg
        (s := s) (p := (2 : ℝ)) (w := w) (f := sqrtH)
        (by norm_num : (1 : ℝ) ≤ 2) hw_nonneg
        (fun i => Real.rpow_nonneg (hH_nonneg i) _)
  have hsquares :
      (∑ i ∈ s, w i * sqrtH i ^ (2 : ℝ)) = B := by
    dsimp [B, sqrtH]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hsqrt_sq : Real.rpow (H i) (1 / 2 : ℝ) ^ 2 = H i :=
      Homogenization.sq_rpow_half_eq_self_of_nonneg (hH_nonneg i)
    have hsqrt_sq_rpow :
        Real.rpow (H i) (1 / 2 : ℝ) ^ (2 : ℝ) = H i := by
      calc
        Real.rpow (H i) (1 / 2 : ℝ) ^ (2 : ℝ) =
            Real.rpow (H i) (1 / 2 : ℝ) ^ 2 := Real.rpow_natCast _ 2
        _ = H i := hsqrt_sq
    exact congrArg (fun x : ℝ => w i * x) hsqrt_sq_rpow
  have hW_rpow_le_one : W ^ (1 / 2 : ℝ) ≤ 1 := by
    have hpow := Real.rpow_le_rpow hW_nonneg hw_sum (by norm_num : 0 ≤ (1 / 2 : ℝ))
    simpa [W] using hpow
  have hright_le_sqrtB :
      W ^ (1 - (2 : ℝ)⁻¹) *
          (∑ i ∈ s, w i * sqrtH i ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ ≤
        Real.rpow B (1 / 2 : ℝ) := by
    have hleftExp : 1 - (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    have hrightExp : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    calc
      W ^ (1 - (2 : ℝ)⁻¹) *
          (∑ i ∈ s, w i * sqrtH i ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹
          = W ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) := by
            rw [hsquares, hleftExp, hrightExp]
      _ ≤ 1 * Real.rpow B (1 / 2 : ℝ) := by
            exact mul_le_mul hW_rpow_le_one le_rfl
              (Real.rpow_nonneg hB_nonneg _) (by norm_num)
      _ = Real.rpow B (1 / 2 : ℝ) := by ring
  have hsum_le_sqrtB :
      ∑ i ∈ s, w i * Real.rpow (H i) (1 / 2 : ℝ) ≤
        Real.rpow B (1 / 2 : ℝ) := by
    simpa [sqrtH] using hholder.trans hright_le_sqrtB
  have hsum_nonneg :
      0 ≤ ∑ i ∈ s, w i * Real.rpow (H i) (1 / 2 : ℝ) := by
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (hw_nonneg i) (Real.rpow_nonneg (hH_nonneg i) _)
  have hsq :=
    pow_le_pow_left₀ hsum_nonneg hsum_le_sqrtB 2
  calc
    (∑ i ∈ s, w i * Real.rpow (H i) (1 / 2 : ℝ)) ^ 2
        ≤ Real.rpow B (1 / 2 : ℝ) ^ 2 := hsq
    _ = B := Homogenization.sq_rpow_half_eq_self_of_nonneg hB_nonneg
    _ = ∑ i ∈ s, w i * H i := rfl

theorem section52_sq_finset_sum_weighted_rpow_half_le_weight_sum_mul_finset_sum_weighted
    {ι : Type*} (s : Finset ι) {w H : ι → ℝ}
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hH_nonneg : ∀ i, 0 ≤ H i) :
    (∑ i ∈ s, w i * Real.rpow (H i) (1 / 2 : ℝ)) ^ 2 ≤
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * H i) := by
  classical
  let sqrtH : ι → ℝ := fun i => Real.rpow (H i) (1 / 2 : ℝ)
  let W : ℝ := ∑ i ∈ s, w i
  let B : ℝ := ∑ i ∈ s, w i * H i
  have hW_nonneg : 0 ≤ W := by
    dsimp [W]
    exact Finset.sum_nonneg fun i _hi => hw_nonneg i
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg fun i _hi => mul_nonneg (hw_nonneg i) (hH_nonneg i)
  have hholder :
      ∑ i ∈ s, w i * sqrtH i ≤
        W ^ (1 - (2 : ℝ)⁻¹) *
          (∑ i ∈ s, w i * sqrtH i ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ := by
    simpa [W, sqrtH] using
      Real.inner_le_weight_mul_Lp_of_nonneg
        (s := s) (p := (2 : ℝ)) (w := w) (f := sqrtH)
        (by norm_num : (1 : ℝ) ≤ 2) hw_nonneg
        (fun i => Real.rpow_nonneg (hH_nonneg i) _)
  have hsquares :
      (∑ i ∈ s, w i * sqrtH i ^ (2 : ℝ)) = B := by
    dsimp [B, sqrtH]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hsqrt_sq : Real.rpow (H i) (1 / 2 : ℝ) ^ 2 = H i :=
      Homogenization.sq_rpow_half_eq_self_of_nonneg (hH_nonneg i)
    have hsqrt_sq_rpow :
        Real.rpow (H i) (1 / 2 : ℝ) ^ (2 : ℝ) = H i := by
      calc
        Real.rpow (H i) (1 / 2 : ℝ) ^ (2 : ℝ) =
            Real.rpow (H i) (1 / 2 : ℝ) ^ 2 := Real.rpow_natCast _ 2
        _ = H i := hsqrt_sq
    exact congrArg (fun x : ℝ => w i * x) hsqrt_sq_rpow
  have hright_eq :
      W ^ (1 - (2 : ℝ)⁻¹) *
          (∑ i ∈ s, w i * sqrtH i ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ =
        W ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) := by
    have hleftExp : 1 - (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    have hrightExp : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    rw [hsquares, hleftExp, hrightExp]
  have hsum_nonneg :
      0 ≤ ∑ i ∈ s, w i * Real.rpow (H i) (1 / 2 : ℝ) := by
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (hw_nonneg i) (Real.rpow_nonneg (hH_nonneg i) _)
  have hholder2 :
      ∑ i ∈ s, w i * sqrtH i ≤
        W ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) := by
    calc
      ∑ i ∈ s, w i * sqrtH i ≤
          W ^ (1 - (2 : ℝ)⁻¹) *
            (∑ i ∈ s, w i * sqrtH i ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ := hholder
      _ = W ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) := hright_eq
  have hsq :=
    pow_le_pow_left₀ hsum_nonneg hholder2 2
  have hsq' :
      (∑ i ∈ s, w i * Real.rpow (H i) (1 / 2 : ℝ)) ^ 2 ≤
        (W ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ)) ^ 2 := by
    simpa [sqrtH] using hsq
  calc
    (∑ i ∈ s, w i * Real.rpow (H i) (1 / 2 : ℝ)) ^ 2
        ≤ (W ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ)) ^ 2 := hsq'
    _ = W * B := by
      have hWsq : (W ^ (1 / 2 : ℝ)) ^ 2 = W :=
        Homogenization.sq_rpow_half_eq_self_of_nonneg hW_nonneg
      have hBsq : (B ^ (1 / 2 : ℝ)) ^ 2 = B :=
        Homogenization.sq_rpow_half_eq_self_of_nonneg hB_nonneg
      rw [mul_pow, hWsq, hBsq]
    _ = (∑ i ∈ s, w i) * (∑ i ∈ s, w i * H i) := rfl

/-- Root decomposition for the upper ellipticity factor:
`||Λ_m||_ξ <= \barσ_0 + ||(Λ_m-\barσ_0)_+||_ξ`. -/
theorem LambdaMomentAtScale_le_barSigma_zero_add_positiveExcessMomentAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {m : ℤ} {s : ℝ} {ξ : ℕ}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hξ : 1 ≤ ξ) (hs : 0 < s)
    (hBarSigma0_nonneg : 0 ≤ hP.barSigmaAtScale hStruct 0)
    (hUpperMeas :
      AEMeasurable
        (fun a : RegCoeffField d =>
          Ch04.LambdaSqCoeffField (originCube d m) s (.finite 1) a) P)
    (hUpperPowInt :
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.LambdaSqCoeffField (originCube d m) s (.finite 1) a) ^ ξ) P)
    (hUpperExcessPowInt :
      Integrable
        (fun a : RegCoeffField d =>
          (max
            (Ch04.LambdaSqCoeffField (originCube d m) s (.finite 1) a -
              hP.barSigmaAtScale hStruct 0)
            0) ^ ξ) P) :
    Ch04.LambdaMomentAtScale P m s ξ ≤
      hP.barSigmaAtScale hStruct 0 +
        LambdaPositiveExcessMomentAtScale P m s ξ hP hStruct := by
  let X : RegCoeffField d → ℝ :=
    fun a => Ch04.LambdaSqCoeffField (originCube d m) s (.finite 1) a
  let E : RegCoeffField d → ℝ :=
    fun a => max (X a - hP.barSigmaAtScale hStruct 0) 0
  have hX_meas : AEMeasurable X P := by
    simpa [X] using hUpperMeas
  have hX_pow_int : Integrable (fun a => X a ^ ξ) P := by
    simpa [X] using hUpperPowInt
  have hE_pow_int : Integrable (fun a => E a ^ ξ) P := by
    simpa [E, X] using hUpperExcessPowInt
  have hE_meas : AEMeasurable E P := by
    exact (hX_meas.sub aemeasurable_const).max aemeasurable_const
  have hX_abs_int : Integrable (fun a => |X a| ^ ξ) P := by
    refine hX_pow_int.congr ?_
    filter_upwards with a
    simp [X, abs_of_nonneg
      (Ch04.LambdaSqCoeffField_finite_nonneg (originCube d m) a hs
        (by norm_num : (1 : ℝ) ≤ 1))]
  have hE_abs_int : Integrable (fun a => |E a| ^ ξ) P := by
    refine hE_pow_int.congr ?_
    filter_upwards with a
    simp [E, abs_of_nonneg (le_max_right (X a - hP.barSigmaAtScale hStruct 0) 0)]
  simpa [Ch04.LambdaMomentAtScale, LambdaPositiveExcessMomentAtScale, X, E] using
    Ch04.annealedMomentRoot_le_const_add_of_nonneg_le
      (P := P) (ξ := ξ) (X := X) (E := E)
      (A := hP.barSigmaAtScale hStruct 0)
      hξ hBarSigma0_nonneg
      (fun a =>
        Ch04.LambdaSqCoeffField_finite_nonneg (originCube d m) a hs
          (by norm_num : (1 : ℝ) ≤ 1))
      (fun a => le_max_right (X a - hP.barSigmaAtScale hStruct 0) 0)
      (fun a => real_le_base_add_max_sub_base_zero (X a) (hP.barSigmaAtScale hStruct 0))
      hX_meas hE_meas hX_abs_int hE_abs_int

/-- Root decomposition for the lower inverse ellipticity factor:
`||λ_m^{-1}||_ξ <= \barσ_{*,0}^{-1} +
||(λ_m^{-1}-\barσ_{*,0}^{-1})_+||_ξ`. -/
theorem lambdaInvMomentAtScale_le_barSigmaStar_zero_inv_add_positiveExcessMomentAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {m : ℤ} {s : ℝ} {ξ : ℕ}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hξ : 1 ≤ ξ) (hs : 0 < s)
    (hBarSigmaStar0_inv_nonneg : 0 ≤ (hP.barSigmaStarAtScale hStruct 0)⁻¹)
    (hLowerMeas :
      AEMeasurable
        (fun a : RegCoeffField d =>
          (Ch04.lambdaSqCoeffField (originCube d m) s (.finite 1) a)⁻¹) P)
    (hLowerPowInt :
      Integrable
        (fun a : RegCoeffField d =>
          ((Ch04.lambdaSqCoeffField (originCube d m) s (.finite 1) a)⁻¹) ^ ξ) P)
    (hLowerExcessPowInt :
      Integrable
        (fun a : RegCoeffField d =>
          (max
            ((Ch04.lambdaSqCoeffField (originCube d m) s (.finite 1) a)⁻¹ -
              (hP.barSigmaStarAtScale hStruct 0)⁻¹)
            0) ^ ξ) P) :
    Ch04.lambdaInvMomentAtScale P m s ξ ≤
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ +
        lambdaInvPositiveExcessMomentAtScale P m s ξ hP hStruct := by
  let X : RegCoeffField d → ℝ :=
    fun a => (Ch04.lambdaSqCoeffField (originCube d m) s (.finite 1) a)⁻¹
  let E : RegCoeffField d → ℝ :=
    fun a => max (X a - (hP.barSigmaStarAtScale hStruct 0)⁻¹) 0
  have hX_meas : AEMeasurable X P := by
    simpa [X] using hLowerMeas
  have hX_pow_int : Integrable (fun a => X a ^ ξ) P := by
    simpa [X] using hLowerPowInt
  have hE_pow_int : Integrable (fun a => E a ^ ξ) P := by
    simpa [E, X] using hLowerExcessPowInt
  have hE_meas : AEMeasurable E P := by
    exact (hX_meas.sub aemeasurable_const).max aemeasurable_const
  have hX_abs_int : Integrable (fun a => |X a| ^ ξ) P := by
    refine hX_pow_int.congr ?_
    filter_upwards with a
    simp [X, abs_of_nonneg
      (inv_nonneg.mpr
        (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d m) a hs
          (by norm_num : (1 : ℝ) ≤ 1)))]
  have hE_abs_int : Integrable (fun a => |E a| ^ ξ) P := by
    refine hE_pow_int.congr ?_
    filter_upwards with a
    simp [E, abs_of_nonneg
      (le_max_right (X a - (hP.barSigmaStarAtScale hStruct 0)⁻¹) 0)]
  simpa [Ch04.lambdaInvMomentAtScale, lambdaInvPositiveExcessMomentAtScale, X, E] using
    Ch04.annealedMomentRoot_le_const_add_of_nonneg_le
      (P := P) (ξ := ξ) (X := X) (E := E)
      (A := (hP.barSigmaStarAtScale hStruct 0)⁻¹)
      hξ hBarSigmaStar0_inv_nonneg
      (fun a =>
        inv_nonneg.mpr
          (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d m) a hs
            (by norm_num : (1 : ℝ) ≤ 1)))
      (fun a => le_max_right (X a - (hP.barSigmaStarAtScale hStruct 0)⁻¹) 0)
      (fun a => real_le_base_add_max_sub_base_zero (X a)
        ((hP.barSigmaStarAtScale hStruct 0)⁻¹))
      hX_meas hE_meas hX_abs_int hE_abs_int

/-- Product assembly for the "in particular" estimate in the multiscale
ellipticity moment lemma.

Once the two component positive-excess estimates are known, this theorem is
the Ch5 algebra turning them into a bound for `widetildeTheta_m`. -/
theorem widetildeThetaAtScale_le_thetaAtScale_zero_add_positiveExcess_products
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℤ)
    (hUpper :
      Ch04.LambdaMomentAtScale P m hP4.sUpper hP4.xi ≤
        hP.barSigmaAtScale hStruct 0 +
          LambdaPositiveExcessMomentAtScale P m hP4.sUpper hP4.xi hP hStruct)
    (hLower :
      Ch04.lambdaInvMomentAtScale P m hP4.sLower hP4.xi ≤
        (hP.barSigmaStarAtScale hStruct 0)⁻¹ +
          lambdaInvPositiveExcessMomentAtScale P m hP4.sLower hP4.xi hP hStruct)
    (hUpper0 :
      hP.barSigmaAtScale hStruct 0 ≤
        Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi)
    (hLower0 :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)
    (hBarSigma0_nonneg : 0 ≤ hP.barSigmaAtScale hStruct 0) :
    widetildeThetaAtScale P m hP4 ≤
      thetaAtScale hP hStruct 0 +
        LambdaPositiveExcessMomentAtScale P m hP4.sUpper hP4.xi hP hStruct *
          Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi +
        lambdaInvPositiveExcessMomentAtScale P m hP4.sLower hP4.xi hP hStruct *
          Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
        LambdaPositiveExcessMomentAtScale P m hP4.sUpper hP4.xi hP hStruct *
          lambdaInvPositiveExcessMomentAtScale P m hP4.sLower hP4.xi hP hStruct := by
  let Lm := Ch04.LambdaMomentAtScale P m hP4.sUpper hP4.xi
  let lm := Ch04.lambdaInvMomentAtScale P m hP4.sLower hP4.xi
  let L0 := Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi
  let l0 := Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi
  let b0 := hP.barSigmaAtScale hStruct 0
  let s0 := (hP.barSigmaStarAtScale hStruct 0)⁻¹
  let UE := LambdaPositiveExcessMomentAtScale P m hP4.sUpper hP4.xi hP hStruct
  let LE := lambdaInvPositiveExcessMomentAtScale P m hP4.sLower hP4.xi hP hStruct
  have hLm_nonneg : 0 ≤ Lm := by
    simpa [Lm] using
      Ch04.LambdaMomentAtScale_nonneg P m hP4.xi hP4.sUpper_pos
  have hlm_nonneg : 0 ≤ lm := by
    simpa [lm] using
      Ch04.lambdaInvMomentAtScale_nonneg P m hP4.xi hP4.sLower_pos
  have hUE_nonneg : 0 ≤ UE := by
    simpa [UE] using
      LambdaPositiveExcessMomentAtScale_nonneg hP4.sUpper hP4.xi hP hStruct m
  have hLE_nonneg : 0 ≤ LE := by
    simpa [LE] using
      lambdaInvPositiveExcessMomentAtScale_nonneg hP4.sLower hP4.xi hP hStruct m
  have hUpper' : Lm ≤ b0 + UE := by
    simpa [Lm, b0, UE] using hUpper
  have hLower' : lm ≤ s0 + LE := by
    simpa [lm, s0, LE] using hLower
  have hUpper0' : b0 ≤ L0 := by
    simpa [b0, L0] using hUpper0
  have hLower0' : s0 ≤ l0 := by
    simpa [s0, l0] using hLower0
  have hUpperRhs_nonneg : 0 ≤ b0 + UE := by
    exact add_nonneg (by simpa [b0] using hBarSigma0_nonneg) hUE_nonneg
  have hProd : Lm * lm ≤ (b0 + UE) * (s0 + LE) :=
    mul_le_mul hUpper' hLower' hlm_nonneg hUpperRhs_nonneg
  have hUEs0 : UE * s0 ≤ UE * l0 :=
    mul_le_mul_of_nonneg_left hLower0' hUE_nonneg
  have hLEb0 : LE * b0 ≤ LE * L0 :=
    mul_le_mul_of_nonneg_left hUpper0' hLE_nonneg
  have hExpand :
      (b0 + UE) * (s0 + LE) ≤ b0 * s0 + UE * l0 + LE * L0 + UE * LE := by
    calc
      (b0 + UE) * (s0 + LE) = b0 * s0 + UE * s0 + LE * b0 + UE * LE := by ring
      _ ≤ b0 * s0 + UE * l0 + LE * L0 + UE * LE :=
        add_le_add (add_le_add (add_le_add le_rfl hUEs0) hLEb0) le_rfl
  calc
    widetildeThetaAtScale P m hP4 = Lm * lm := by
      simp [widetildeThetaAtScale, Ch04.widetildeThetaAtScale, Lm, lm]
    _ ≤ (b0 + UE) * (s0 + LE) := hProd
    _ ≤ b0 * s0 + UE * l0 + LE * L0 + UE * LE := hExpand
    _ =
        thetaAtScale hP hStruct 0 +
          UE * l0 + LE * L0 + UE * LE := by
        simp [thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale, b0, s0]
    _ =
        thetaAtScale hP hStruct 0 +
          LambdaPositiveExcessMomentAtScale P m hP4.sUpper hP4.xi hP hStruct *
            Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi +
          lambdaInvPositiveExcessMomentAtScale P m hP4.sLower hP4.xi hP hStruct *
            Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
          LambdaPositiveExcessMomentAtScale P m hP4.sUpper hP4.xi hP hStruct *
            lambdaInvPositiveExcessMomentAtScale P m hP4.sLower hP4.xi hP hStruct := by
        simp [UE, LE, L0, l0]

/-- Product assembly with the two positive-excess roots already bounded by
unit-scale moment roots. This is the final algebraic step in the Section 5.2
moment lemma. -/
theorem widetildeThetaAtScale_le_thetaAtScale_zero_add_error_of_positiveExcess_bounds
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℤ)
    {coeffUpper coeffLower finalCoeff : ℝ}
    (hUpper :
      Ch04.LambdaMomentAtScale P m hP4.sUpper hP4.xi ≤
        hP.barSigmaAtScale hStruct 0 +
          LambdaPositiveExcessMomentAtScale P m hP4.sUpper hP4.xi hP hStruct)
    (hLower :
      Ch04.lambdaInvMomentAtScale P m hP4.sLower hP4.xi ≤
        (hP.barSigmaStarAtScale hStruct 0)⁻¹ +
          lambdaInvPositiveExcessMomentAtScale P m hP4.sLower hP4.xi hP hStruct)
    (hUpper0 :
      hP.barSigmaAtScale hStruct 0 ≤
        Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi)
    (hLower0 :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)
    (hBarSigma0_nonneg : 0 ≤ hP.barSigmaAtScale hStruct 0)
    (hCoeffUpper_nonneg : 0 ≤ coeffUpper)
    (_hCoeffLower_nonneg : 0 ≤ coeffLower)
    (hUpperExcess :
      LambdaPositiveExcessMomentAtScale P m hP4.sUpper hP4.xi hP hStruct ≤
        coeffUpper * Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi)
    (hLowerExcess :
      lambdaInvPositiveExcessMomentAtScale P m hP4.sLower hP4.xi hP hStruct ≤
        coeffLower * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)
    (hCoeff :
      coeffUpper + coeffLower + coeffUpper * coeffLower ≤ finalCoeff) :
    widetildeThetaAtScale P m hP4 ≤
      thetaAtScale hP hStruct 0 +
        finalCoeff * widetildeThetaAtScale P 0 hP4 := by
  let L0 := Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi
  let l0 := Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi
  let UE := LambdaPositiveExcessMomentAtScale P m hP4.sUpper hP4.xi hP hStruct
  let LE := lambdaInvPositiveExcessMomentAtScale P m hP4.sLower hP4.xi hP hStruct
  have hL0_nonneg : 0 ≤ L0 := by
    simpa [L0] using Ch04.LambdaMomentAtScale_nonneg P 0 hP4.xi hP4.sUpper_pos
  have hl0_nonneg : 0 ≤ l0 := by
    simpa [l0] using Ch04.lambdaInvMomentAtScale_nonneg P 0 hP4.xi hP4.sLower_pos
  have hUE_nonneg : 0 ≤ UE := by
    simpa [UE] using
      LambdaPositiveExcessMomentAtScale_nonneg hP4.sUpper hP4.xi hP hStruct m
  have hLE_nonneg : 0 ≤ LE := by
    simpa [LE] using
      lambdaInvPositiveExcessMomentAtScale_nonneg hP4.sLower hP4.xi hP hStruct m
  have hBase_nonneg : 0 ≤ L0 * l0 := mul_nonneg hL0_nonneg hl0_nonneg
  have hProduct :
      widetildeThetaAtScale P m hP4 ≤
        thetaAtScale hP hStruct 0 + UE * l0 + LE * L0 + UE * LE := by
    simpa [UE, LE, L0, l0] using
      widetildeThetaAtScale_le_thetaAtScale_zero_add_positiveExcess_products
        hP hStruct hP4 m hUpper hLower hUpper0 hLower0 hBarSigma0_nonneg
  have hUE_le : UE ≤ coeffUpper * L0 := by
    simpa [UE, L0] using hUpperExcess
  have hLE_le : LE ≤ coeffLower * l0 := by
    simpa [LE, l0] using hLowerExcess
  have hTermUpper : UE * l0 ≤ coeffUpper * (L0 * l0) := by
    have h := mul_le_mul_of_nonneg_right hUE_le hl0_nonneg
    calc
      UE * l0 ≤ (coeffUpper * L0) * l0 := h
      _ = coeffUpper * (L0 * l0) := by ring
  have hTermLower : LE * L0 ≤ coeffLower * (L0 * l0) := by
    have h := mul_le_mul_of_nonneg_right hLE_le hL0_nonneg
    calc
      LE * L0 ≤ (coeffLower * l0) * L0 := h
      _ = coeffLower * (L0 * l0) := by ring
  have hTermMixed : UE * LE ≤ coeffUpper * coeffLower * (L0 * l0) := by
    have hUpperRhs_nonneg : 0 ≤ coeffUpper * L0 :=
      mul_nonneg hCoeffUpper_nonneg hL0_nonneg
    have h := mul_le_mul hUE_le hLE_le hLE_nonneg hUpperRhs_nonneg
    calc
      UE * LE ≤ (coeffUpper * L0) * (coeffLower * l0) := h
      _ = coeffUpper * coeffLower * (L0 * l0) := by ring
  have hError :
      UE * l0 + LE * L0 + UE * LE ≤
        (coeffUpper + coeffLower + coeffUpper * coeffLower) * (L0 * l0) := by
    calc
      UE * l0 + LE * L0 + UE * LE
          ≤
        coeffUpper * (L0 * l0) + coeffLower * (L0 * l0) +
          coeffUpper * coeffLower * (L0 * l0) :=
        add_le_add (add_le_add hTermUpper hTermLower) hTermMixed
      _ = (coeffUpper + coeffLower + coeffUpper * coeffLower) * (L0 * l0) := by ring
  have hCoeffError :
      (coeffUpper + coeffLower + coeffUpper * coeffLower) * (L0 * l0) ≤
        finalCoeff * (L0 * l0) :=
    mul_le_mul_of_nonneg_right hCoeff hBase_nonneg
  calc
    widetildeThetaAtScale P m hP4
        ≤ thetaAtScale hP hStruct 0 + UE * l0 + LE * L0 + UE * LE := hProduct
    _ = thetaAtScale hP hStruct 0 + (UE * l0 + LE * L0 + UE * LE) := by ring
    _ ≤ thetaAtScale hP hStruct 0 +
        (coeffUpper + coeffLower + coeffUpper * coeffLower) * (L0 * l0) :=
      add_le_add_right hError _
    _ ≤ thetaAtScale hP hStruct 0 + finalCoeff * (L0 * l0) :=
      add_le_add_right hCoeffError _
    _ = thetaAtScale hP hStruct 0 +
        finalCoeff * widetildeThetaAtScale P 0 hP4 := by
      simp [widetildeThetaAtScale, Ch04.widetildeThetaAtScale, L0, l0]

/-- Final product algebra from an already assembled positive-excess product
bound. This is useful when the scalar root decomposition has already been
proved upstream. -/
theorem widetildeThetaAtScale_le_thetaAtScale_zero_add_error_of_positiveExcess_product_bound
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℤ)
    {coeffUpper coeffLower finalCoeff : ℝ}
    (hProduct :
      widetildeThetaAtScale P m hP4 ≤
        thetaAtScale hP hStruct 0 +
          LambdaPositiveExcessMomentAtScale P m hP4.sUpper hP4.xi hP hStruct *
            Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi +
          lambdaInvPositiveExcessMomentAtScale P m hP4.sLower hP4.xi hP hStruct *
            Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
          LambdaPositiveExcessMomentAtScale P m hP4.sUpper hP4.xi hP hStruct *
            lambdaInvPositiveExcessMomentAtScale P m hP4.sLower hP4.xi hP hStruct)
    (hCoeffUpper_nonneg : 0 ≤ coeffUpper)
    (_hCoeffLower_nonneg : 0 ≤ coeffLower)
    (hUpperExcess :
      LambdaPositiveExcessMomentAtScale P m hP4.sUpper hP4.xi hP hStruct ≤
        coeffUpper * Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi)
    (hLowerExcess :
      lambdaInvPositiveExcessMomentAtScale P m hP4.sLower hP4.xi hP hStruct ≤
        coeffLower * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)
    (hCoeff :
      coeffUpper + coeffLower + coeffUpper * coeffLower ≤ finalCoeff) :
    widetildeThetaAtScale P m hP4 ≤
      thetaAtScale hP hStruct 0 +
        finalCoeff * widetildeThetaAtScale P 0 hP4 := by
  let L0 := Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi
  let l0 := Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi
  let UE := LambdaPositiveExcessMomentAtScale P m hP4.sUpper hP4.xi hP hStruct
  let LE := lambdaInvPositiveExcessMomentAtScale P m hP4.sLower hP4.xi hP hStruct
  have hL0_nonneg : 0 ≤ L0 := by
    simpa [L0] using Ch04.LambdaMomentAtScale_nonneg P 0 hP4.xi hP4.sUpper_pos
  have hl0_nonneg : 0 ≤ l0 := by
    simpa [l0] using Ch04.lambdaInvMomentAtScale_nonneg P 0 hP4.xi hP4.sLower_pos
  have hUE_nonneg : 0 ≤ UE := by
    simpa [UE] using
      LambdaPositiveExcessMomentAtScale_nonneg hP4.sUpper hP4.xi hP hStruct m
  have hLE_nonneg : 0 ≤ LE := by
    simpa [LE] using
      lambdaInvPositiveExcessMomentAtScale_nonneg hP4.sLower hP4.xi hP hStruct m
  have hBase_nonneg : 0 ≤ L0 * l0 := mul_nonneg hL0_nonneg hl0_nonneg
  have hProduct' :
      widetildeThetaAtScale P m hP4 ≤
        thetaAtScale hP hStruct 0 + UE * l0 + LE * L0 + UE * LE := by
    simpa [UE, LE, L0, l0] using hProduct
  have hUE_le : UE ≤ coeffUpper * L0 := by
    simpa [UE, L0] using hUpperExcess
  have hLE_le : LE ≤ coeffLower * l0 := by
    simpa [LE, l0] using hLowerExcess
  have hTermUpper : UE * l0 ≤ coeffUpper * (L0 * l0) := by
    have h := mul_le_mul_of_nonneg_right hUE_le hl0_nonneg
    calc
      UE * l0 ≤ (coeffUpper * L0) * l0 := h
      _ = coeffUpper * (L0 * l0) := by ring
  have hTermLower : LE * L0 ≤ coeffLower * (L0 * l0) := by
    have h := mul_le_mul_of_nonneg_right hLE_le hL0_nonneg
    calc
      LE * L0 ≤ (coeffLower * l0) * L0 := h
      _ = coeffLower * (L0 * l0) := by ring
  have hTermMixed : UE * LE ≤ coeffUpper * coeffLower * (L0 * l0) := by
    have hUpperRhs_nonneg : 0 ≤ coeffUpper * L0 :=
      mul_nonneg hCoeffUpper_nonneg hL0_nonneg
    have h := mul_le_mul hUE_le hLE_le hLE_nonneg hUpperRhs_nonneg
    calc
      UE * LE ≤ (coeffUpper * L0) * (coeffLower * l0) := h
      _ = coeffUpper * coeffLower * (L0 * l0) := by ring
  have hError :
      UE * l0 + LE * L0 + UE * LE ≤
        (coeffUpper + coeffLower + coeffUpper * coeffLower) * (L0 * l0) := by
    calc
      UE * l0 + LE * L0 + UE * LE
          ≤
        coeffUpper * (L0 * l0) + coeffLower * (L0 * l0) +
          coeffUpper * coeffLower * (L0 * l0) :=
        add_le_add (add_le_add hTermUpper hTermLower) hTermMixed
      _ = (coeffUpper + coeffLower + coeffUpper * coeffLower) * (L0 * l0) := by ring
  have hCoeffError :
      (coeffUpper + coeffLower + coeffUpper * coeffLower) * (L0 * l0) ≤
        finalCoeff * (L0 * l0) :=
    mul_le_mul_of_nonneg_right hCoeff hBase_nonneg
  calc
    widetildeThetaAtScale P m hP4
        ≤ thetaAtScale hP hStruct 0 + UE * l0 + LE * L0 + UE * LE := hProduct'
    _ = thetaAtScale hP hStruct 0 + (UE * l0 + LE * L0 + UE * LE) := by ring
    _ ≤ thetaAtScale hP hStruct 0 +
        (coeffUpper + coeffLower + coeffUpper * coeffLower) * (L0 * l0) := by
      exact add_le_add_right hError _
    _ ≤ thetaAtScale hP hStruct 0 + finalCoeff * (L0 * l0) := by
      exact add_le_add_right hCoeffError _
    _ = thetaAtScale hP hStruct 0 +
        finalCoeff * widetildeThetaAtScale P 0 hP4 := by
      simp [widetildeThetaAtScale, Ch04.widetildeThetaAtScale, L0, l0]

end

end Section52
end Ch05
end Book
end Homogenization
