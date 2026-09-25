/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.PairedSquares

/-! # Paired Weak Norm Squares -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundCoarseFluctuations

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

/-!
# Paired weak-norm square conversion

This proof-internal file converts the actual paired weak-norm square
expectations from the first Section 5.3 lemma into the coarse-fluctuation
manuscript terms.  The component expectation estimates live in the preceding
files; this file owns the final square algebra.
-/

noncomputable section

private theorem rhsSum_nonneg
    {A B R D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    0 ≤ A + B + R + D := by
  nlinarith

private theorem first_le_rhsSum
    {A B R D : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    A ≤ A + B + R + D := by
  nlinarith

private theorem middle_pair_le_rhsSum
    {A B R D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) :
    B + R ≤ A + B + R + D := by
  nlinarith

private theorem last_pair_le_rhsSum
    {A B R D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    D + R ≤ A + B + R + D := by
  nlinarith

private theorem fourth_le_rhsSum
    {A B R D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    D ≤ A + B + R + D := by
  nlinarith

private theorem pairedConstant_nonneg
    {CH CM CL K : ℝ} (hCH : 0 ≤ CH) (hCM : 0 ≤ CM) (hCL : 0 ≤ CL) :
    0 ≤ CH + K ^ 2 * CM + K ^ 2 * CL + 2 * K ^ 2 := by
  have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
  nlinarith

private theorem pairedComponentSum_le
    {H M L T Ssum CH CM CL K C0 : ℝ}
    (hH : H ≤ CH * Ssum) (hM : M ≤ CM * Ssum)
    (hL : L ≤ CL * Ssum) (hT : T ≤ 2 * Ssum)
    (hK2 : 0 ≤ K ^ 2)
    (hC0 : C0 = CH + K ^ 2 * CM + K ^ 2 * CL + 2 * K ^ 2) :
    H + K ^ 2 * M + K ^ 2 * L + K ^ 2 * T ≤ C0 * Ssum := by
  have hKM : K ^ 2 * M ≤ K ^ 2 * (CM * Ssum) :=
    mul_le_mul_of_nonneg_left hM hK2
  have hKL : K ^ 2 * L ≤ K ^ 2 * (CL * Ssum) :=
    mul_le_mul_of_nonneg_left hL hK2
  have hKT : K ^ 2 * T ≤ K ^ 2 * (2 * Ssum) :=
    mul_le_mul_of_nonneg_left hT hK2
  calc
    H + K ^ 2 * M + K ^ 2 * L + K ^ 2 * T
        ≤ CH * Ssum + K ^ 2 * (CM * Ssum) +
            K ^ 2 * (CL * Ssum) + K ^ 2 * (2 * Ssum) := by
          nlinarith
    _ = C0 * Ssum := by
          rw [hC0]
          ring

private theorem sq_sum_four_le_const_sum_sq (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤
      4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

private theorem norm_sq_le_vecNormSq {d : ℕ} (v : Vec d) :
    ‖v‖ ^ 2 ≤ vecNormSq v := by
  have hnorm_le : ‖v‖ ≤ Real.sqrt (vecNormSq v) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 ?_
    intro i
    have hi : ‖v i‖ ^ 2 ≤ vecNormSq v := by
      calc
        ‖v i‖ ^ 2 = v i ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
        _ ≤ ∑ j, v j ^ 2 := by
          exact Finset.single_le_sum (fun j _hj => sq_nonneg (v j)) (Finset.mem_univ i)
        _ = vecNormSq v := by
          simp [vecNormSq, vecDot, pow_two]
    exact Real.le_sqrt_of_sq_le hi
  have hsqrt_sq : (Real.sqrt (vecNormSq v)) ^ 2 = vecNormSq v := by
    simpa [pow_two] using Real.sq_sqrt (vecNormSq_nonneg v)
  calc
    ‖v‖ ^ 2 ≤ (Real.sqrt (vecNormSq v)) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 hnorm_le
    _ = vecNormSq v := hsqrt_sq

private theorem paired_rhsSquares_le_componentSquares
    {σ K AG MG LG CG AF MF LF CF : ℝ} (hσ : 0 ≤ σ) :
    σ * (AG + K * MG + K * LG + K * CG) ^ 2 +
        σ⁻¹ * (AF + K * MF + K * LF + K * CF) ^ 2
      ≤
    4 *
      ((σ * AG ^ 2 + σ⁻¹ * AF ^ 2) +
        K ^ 2 * (σ * MG ^ 2 + σ⁻¹ * MF ^ 2) +
          K ^ 2 * (σ * LG ^ 2 + σ⁻¹ * LF ^ 2) +
            K ^ 2 * (σ * CG ^ 2 + σ⁻¹ * CF ^ 2)) := by
  have hσinv : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ
  have hg := sq_sum_four_le_const_sum_sq AG (K * MG) (K * LG) (K * CG)
  have hf := sq_sum_four_le_const_sum_sq AF (K * MF) (K * LF) (K * CF)
  calc
    σ * (AG + K * MG + K * LG + K * CG) ^ 2 +
        σ⁻¹ * (AF + K * MF + K * LF + K * CF) ^ 2
        ≤
      σ * (4 * (AG ^ 2 + (K * MG) ^ 2 + (K * LG) ^ 2 + (K * CG) ^ 2)) +
        σ⁻¹ * (4 * (AF ^ 2 + (K * MF) ^ 2 + (K * LF) ^ 2 + (K * CF) ^ 2)) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hg hσ)
          (mul_le_mul_of_nonneg_left hf hσinv)
    _ =
      4 *
        ((σ * AG ^ 2 + σ⁻¹ * AF ^ 2) +
          K ^ 2 * (σ * MG ^ 2 + σ⁻¹ * MF ^ 2) +
            K ^ 2 * (σ * LG ^ 2 + σ⁻¹ * LF ^ 2) +
              K ^ 2 * (σ * CG ^ 2 + σ⁻¹ * CF ^ 2)) := by ring

private theorem rpow_three_sq (x : ℝ) :
    Real.rpow (3 : ℝ) x ^ 2 = Real.rpow (3 : ℝ) (2 * x) := by
  calc
    Real.rpow (3 : ℝ) x ^ 2 =
        Real.rpow (3 : ℝ) x * Real.rpow (3 : ℝ) x := by ring
    _ = Real.rpow (3 : ℝ) (x + x) := by
        exact (Real.rpow_add (by norm_num : (0 : ℝ) < 3) x x).symm
    _ = Real.rpow (3 : ℝ) (2 * x) := by ring_nf

private theorem inv_sq_rpow_tail_le
    {β r N : ℝ} (hβ : 0 < β) (hβr : β ≤ r) (hN : 0 ≤ N) :
    r⁻¹ ^ 2 * Real.rpow (3 : ℝ) (-2 * r * N) ≤
      (β ^ 2)⁻¹ * Real.rpow (3 : ℝ) (-2 * β * N) := by
  have hr : 0 < r := hβ.trans_le hβr
  have hinv : r⁻¹ ≤ β⁻¹ := (inv_le_inv₀ hr hβ).2 hβr
  have hinv_sq : r⁻¹ ^ 2 ≤ β⁻¹ ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hr.le) hinv 2
  have hβ_inv_sq : β⁻¹ ^ 2 = (β ^ 2)⁻¹ := by
    field_simp [hβ.ne']
  have hinv_sq' : r⁻¹ ^ 2 ≤ (β ^ 2)⁻¹ := by
    simpa [hβ_inv_sq] using hinv_sq
  have hpow :
      Real.rpow (3 : ℝ) (-2 * r * N) ≤
        Real.rpow (3 : ℝ) (-2 * β * N) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
    nlinarith
  exact mul_le_mul hinv_sq' hpow
    (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    (inv_nonneg.mpr (sq_nonneg β))

private theorem sqrt_sub_one_sq_le_sub_one {θ : ℝ} (hθ : 1 ≤ θ) :
    (Real.sqrt θ - 1) ^ 2 ≤ θ - 1 := by
  have hθ_nonneg : 0 ≤ θ := le_trans zero_le_one hθ
  have hs_nonneg : 0 ≤ Real.sqrt θ - 1 := by
    have hs : 1 ≤ Real.sqrt θ := Real.one_le_sqrt.mpr hθ
    linarith
  have hfactor :
      (Real.sqrt θ - 1) * (Real.sqrt θ + 1) = θ - 1 := by
    calc
      (Real.sqrt θ - 1) * (Real.sqrt θ + 1) =
          (Real.sqrt θ) ^ 2 - 1 := by ring
      _ = θ - 1 := by rw [Real.sq_sqrt hθ_nonneg]
  calc
    (Real.sqrt θ - 1) ^ 2 =
        (Real.sqrt θ - 1) * (Real.sqrt θ - 1) := by ring
    _ ≤ (Real.sqrt θ - 1) * (Real.sqrt θ + 1) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hs_nonneg
    _ = θ - 1 := hfactor

/-- The constant affine tails in the weak-norm maximizer RHS are absorbed by
the low-scale scalar tail of the final manuscript RHS. -/
theorem paired_constantTail_special_le_lowScaleTail
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (_hkm : k < m) (e : Vec d) (he : vecNormSq e = 1) :
    let β := section53CoarseFluctuationBeta hP4
    let s := hP4.sLower + 2 * β
    let t := hP4.sUpper + 2 * β
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
    let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
    let σ := sigmaHatAtScale hP hStruct (m : ℤ)
    let θ := thetaAtScale hP hStruct (m : ℤ)
    σ *
        (WeakNormsMaximizer.gradientConstantTailAtScale
          (m : ℤ) (k : ℤ) s p0_e) ^ 2 +
      σ⁻¹ *
        (WeakNormsMaximizer.fluxConstantTailAtScale
          (m : ℤ) (k : ℤ) t q0_e) ^ 2
      ≤
        2 * ((β ^ 2)⁻¹ *
          Real.rpow (3 : ℝ)
            (-2 * β * (((m - k : ℕ) : ℝ))) *
          coarseFluctuationScalarWeightAtScale hP hStruct m * (θ - 1)) := by
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let t := hP4.sUpper + 2 * β
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let θ := thetaAtScale hP hStruct (m : ℤ)
  let tail :=
    (β ^ 2)⁻¹ *
      Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hs_ge : β ≤ s := by
    dsimp [s, β]
    linarith [hP4.sLower_nonneg, hβ_pos.le]
  have ht_ge : β ≤ t := by
    dsimp [t, β]
    linarith [hP4.sUpper_nonneg, hβ_pos.le]
  have hN_nonneg : 0 ≤ (((m - k : ℕ) : ℝ)) := by positivity
  have hs_factor :
      s⁻¹ ^ 2 *
          Real.rpow (3 : ℝ)
            (-2 * s * (((m - k : ℕ) : ℝ))) ≤ tail := by
    simpa [tail] using inv_sq_rpow_tail_le hβ_pos hs_ge hN_nonneg
  have ht_factor :
      t⁻¹ ^ 2 *
          Real.rpow (3 : ℝ)
            (-2 * t * (((m - k : ℕ) : ℝ))) ≤ tail := by
    simpa [tail] using inv_sq_rpow_tail_le hβ_pos ht_ge hN_nonneg
  have htail_nonneg : 0 ≤ tail := by
    dsimp [tail]
    exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _))
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  have hσ_nonneg : 0 ≤ σ := Real.sqrt_nonneg _
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hθ_one : 1 ≤ θ := by
    simpa [θ] using one_le_thetaAtScale_of_P4 hP hStruct hP4 m
  have hθ_sub_nonneg : 0 ≤ θ - 1 := by linarith
  have hcenter_le : (Real.sqrt θ - 1) ^ 2 ≤ θ - 1 :=
    sqrt_sub_one_sq_le_sub_one hθ_one
  have hp_center :
      σ * ‖p0_e‖ ^ 2 ≤ (Real.sqrt θ - 1) ^ 2 := by
    have hnorm := norm_sq_le_vecNormSq p0_e
    have hvec :=
      sigmaHatAtScale_mul_vecNormSq_specialPCentering_eq hP hStruct hP4 m e
    calc
      σ * ‖p0_e‖ ^ 2 ≤ σ * vecNormSq p0_e :=
        mul_le_mul_of_nonneg_left hnorm hσ_nonneg
      _ = (Real.sqrt θ - 1) ^ 2 := by
        simpa [σ, θ, p_e, q_e, p0_e, he] using hvec
  have hq_center :
      σ⁻¹ * ‖q0_e‖ ^ 2 ≤ (Real.sqrt θ - 1) ^ 2 := by
    have hnorm := norm_sq_le_vecNormSq q0_e
    have hvec :=
      inv_sigmaHatAtScale_mul_vecNormSq_specialQCentering_eq hP hStruct hP4 m e
    calc
      σ⁻¹ * ‖q0_e‖ ^ 2 ≤ σ⁻¹ * vecNormSq q0_e :=
        mul_le_mul_of_nonneg_left hnorm hσ_inv_nonneg
      _ = (Real.sqrt θ - 1) ^ 2 := by
        simpa [σ, θ, p_e, q_e, q0_e, he] using hvec
  have hscalar_one :
      1 ≤ coarseFluctuationScalarWeightAtScale hP hStruct m :=
    one_le_coarseFluctuationScalarWeightAtScale hP hStruct hP4 m
  have hgrad_sq :
      (WeakNormsMaximizer.gradientConstantTailAtScale
          (m : ℤ) (k : ℤ) s p0_e) ^ 2 =
        s⁻¹ ^ 2 *
          Real.rpow (3 : ℝ)
            (-2 * s * (((m - k : ℕ) : ℝ))) * ‖p0_e‖ ^ 2 := by
    dsimp [WeakNormsMaximizer.gradientConstantTailAtScale]
    have hmk :
        (Int.toNat ((m : ℤ) - (k : ℤ)) : ℝ) = ((m - k : ℕ) : ℝ) := by
      have hmk_nat : Int.toNat ((m : ℤ) - (k : ℤ)) = m - k := by omega
      exact_mod_cast hmk_nat
    rw [hmk]
    rw [mul_pow, mul_pow]
    change
      s⁻¹ ^ 2 *
          (Real.rpow (3 : ℝ) (-s * (((m - k : ℕ) : ℝ)))) ^ 2 *
            ‖p0_e‖ ^ 2 =
        s⁻¹ ^ 2 *
          Real.rpow (3 : ℝ) (-2 * s * (((m - k : ℕ) : ℝ))) *
            ‖p0_e‖ ^ 2
    rw [rpow_three_sq]
    ring_nf
  have hflux_sq :
      (WeakNormsMaximizer.fluxConstantTailAtScale
          (m : ℤ) (k : ℤ) t q0_e) ^ 2 =
        t⁻¹ ^ 2 *
          Real.rpow (3 : ℝ)
            (-2 * t * (((m - k : ℕ) : ℝ))) * ‖q0_e‖ ^ 2 := by
    dsimp [WeakNormsMaximizer.fluxConstantTailAtScale]
    have hmk :
        (Int.toNat ((m : ℤ) - (k : ℤ)) : ℝ) = ((m - k : ℕ) : ℝ) := by
      have hmk_nat : Int.toNat ((m : ℤ) - (k : ℤ)) = m - k := by omega
      exact_mod_cast hmk_nat
    rw [hmk]
    rw [mul_pow, mul_pow]
    change
      t⁻¹ ^ 2 *
          (Real.rpow (3 : ℝ) (-t * (((m - k : ℕ) : ℝ)))) ^ 2 *
            ‖q0_e‖ ^ 2 =
        t⁻¹ ^ 2 *
          Real.rpow (3 : ℝ) (-2 * t * (((m - k : ℕ) : ℝ))) *
            ‖q0_e‖ ^ 2
    rw [rpow_three_sq]
    ring_nf
  have hgrad_le :
      σ *
          (WeakNormsMaximizer.gradientConstantTailAtScale
            (m : ℤ) (k : ℤ) s p0_e) ^ 2
        ≤ tail * (θ - 1) := by
    calc
      σ *
          (WeakNormsMaximizer.gradientConstantTailAtScale
            (m : ℤ) (k : ℤ) s p0_e) ^ 2
          =
        (s⁻¹ ^ 2 *
          Real.rpow (3 : ℝ)
            (-2 * s * (((m - k : ℕ) : ℝ)))) *
          (σ * ‖p0_e‖ ^ 2) := by
          rw [hgrad_sq]
          ring
      _ ≤ tail * (θ - 1) := by
          have hp_nonneg : 0 ≤ σ * ‖p0_e‖ ^ 2 :=
            mul_nonneg hσ_nonneg (sq_nonneg _)
          exact mul_le_mul hs_factor (hp_center.trans hcenter_le)
            hp_nonneg htail_nonneg
  have hflux_le :
      σ⁻¹ *
          (WeakNormsMaximizer.fluxConstantTailAtScale
            (m : ℤ) (k : ℤ) t q0_e) ^ 2
        ≤ tail * (θ - 1) := by
    calc
      σ⁻¹ *
          (WeakNormsMaximizer.fluxConstantTailAtScale
            (m : ℤ) (k : ℤ) t q0_e) ^ 2
          =
        (t⁻¹ ^ 2 *
          Real.rpow (3 : ℝ)
            (-2 * t * (((m - k : ℕ) : ℝ)))) *
          (σ⁻¹ * ‖q0_e‖ ^ 2) := by
          rw [hflux_sq]
          ring
      _ ≤ tail * (θ - 1) := by
          have hq_nonneg : 0 ≤ σ⁻¹ * ‖q0_e‖ ^ 2 :=
            mul_nonneg hσ_inv_nonneg (sq_nonneg _)
          exact mul_le_mul ht_factor (hq_center.trans hcenter_le)
            hq_nonneg htail_nonneg
  calc
    σ *
        (WeakNormsMaximizer.gradientConstantTailAtScale
          (m : ℤ) (k : ℤ) s p0_e) ^ 2 +
      σ⁻¹ *
        (WeakNormsMaximizer.fluxConstantTailAtScale
          (m : ℤ) (k : ℤ) t q0_e) ^ 2
        ≤ tail * (θ - 1) + tail * (θ - 1) :=
          add_le_add hgrad_le hflux_le
    _ = 2 * (tail * (θ - 1)) := by ring
    _ ≤
        2 * (tail *
          coarseFluctuationScalarWeightAtScale hP hStruct m * (θ - 1)) := by
        have htail_theta_nonneg : 0 ≤ tail * (θ - 1) :=
          mul_nonneg htail_nonneg hθ_sub_nonneg
        have htail_scalar :
            tail * (θ - 1) ≤
              tail * coarseFluctuationScalarWeightAtScale hP hStruct m *
                (θ - 1) := by
          calc
            tail * (θ - 1) = tail * 1 * (θ - 1) := by ring
            _ ≤ tail * coarseFluctuationScalarWeightAtScale hP hStruct m *
                  (θ - 1) := by
                gcongr
        exact mul_le_mul_of_nonneg_left htail_scalar (by norm_num)
    _ =
        2 * ((β ^ 2)⁻¹ *
          Real.rpow (3 : ℝ)
            (-2 * β * (((m - k : ℕ) : ℝ))) *
          coarseFluctuationScalarWeightAtScale hP hStruct m * (θ - 1)) := by
        simp [tail, mul_assoc]

/-- The paired special-vector weak-norm square expectation is bounded by the
four component square expectations coming from the weak-norm maximizer RHS.
This is the expectation-level square algebra; later lemmas convert the
component integrals into the manuscript coarse-fluctuation terms. -/
theorem paired_weakNormSquares_special_le_componentIntegrals
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m) (e : Vec d) (he : vecNormSq e = 1)
    (hGradSq :
      let β := section53CoarseFluctuationBeta hP4
      let s := hP4.sLower + 2 * β
      let p_e := specialPAtScale hP hStruct (m : ℤ) e
      let q_e := specialQAtScale hP hStruct (m : ℤ) e
      let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.canonicalScalarResponseGradientWeakNormCubeSet
              (originCube d (m : ℤ)) s p_e q_e p0_e a.toFun) ^ 2) P)
    (hFluxSq :
      let β := section53CoarseFluctuationBeta hP4
      let t := hP4.sUpper + 2 * β
      let p_e := specialPAtScale hP hStruct (m : ℤ) e
      let q_e := specialQAtScale hP hStruct (m : ℤ) e
      let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.canonicalScalarResponseFluxWeakNormCubeSet
              (originCube d (m : ℤ)) t p_e q_e q0_e a.toFun) ^ 2) P) :
    let β := section53CoarseFluctuationBeta hP4
    let s := hP4.sLower + 2 * β
    let s' := hP4.sLower + β
    let t := hP4.sUpper + 2 * β
    let t' := hP4.sUpper + β
    let Q : TriadicCube d := originCube d (m : ℤ)
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
    let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
    let σ := sigmaHatAtScale hP hStruct (m : ℤ)
    let K := WeakNormsMaximizer.section53WeakNormMaximizerConst d
    let gradWeak :=
      Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p_e q_e p0_e
    let fluxWeak :=
      Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p_e q_e q0_e
    σ * (∫ a, (gradWeak a) ^ 2 ∂P) +
        σ⁻¹ * (∫ a, (fluxWeak a) ^ 2 ∂P)
      ≤
    16 *
      ((∫ a,
          (σ *
              (WeakNormsMaximizer.gradientAverageTermAtScale
                (m : ℤ) (k : ℤ) s p_e q_e p0_e a) ^ 2 +
            σ⁻¹ *
              (WeakNormsMaximizer.fluxAverageTermAtScale
                (m : ℤ) (k : ℤ) t p_e q_e q0_e a) ^ 2) ∂P) +
        K ^ 2 *
          (∫ a,
            (σ *
                (WeakNormsMaximizer.gradientMismatchTermAtScale
                  (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
              σ⁻¹ *
                (WeakNormsMaximizer.fluxMismatchTermAtScale
                  (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) ∂P) +
        K ^ 2 *
          (∫ a,
            (σ *
                (WeakNormsMaximizer.gradientLowScaleTailAtScale
                  (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
              σ⁻¹ *
                (WeakNormsMaximizer.fluxLowScaleTailAtScale
                  (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) ∂P) +
        K ^ 2 *
          (σ *
              (WeakNormsMaximizer.gradientConstantTailAtScale
                (m : ℤ) (k : ℤ) s p0_e) ^ 2 +
            σ⁻¹ *
              (WeakNormsMaximizer.fluxConstantTailAtScale
                (m : ℤ) (k : ℤ) t q0_e) ^ 2)) := by
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let s' := hP4.sLower + β
  let t := hP4.sUpper + 2 * β
  let t' := hP4.sUpper + β
  let Q : TriadicCube d := originCube d (m : ℤ)
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let K := WeakNormsMaximizer.section53WeakNormMaximizerConst d
  let gradWeak :=
    Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p_e q_e p0_e
  let fluxWeak :=
    Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p_e q_e q0_e
  let H : RegCoeffField d → ℝ := fun a =>
    σ *
        (WeakNormsMaximizer.gradientAverageTermAtScale
          (m : ℤ) (k : ℤ) s p_e q_e p0_e a) ^ 2 +
      σ⁻¹ *
        (WeakNormsMaximizer.fluxAverageTermAtScale
          (m : ℤ) (k : ℤ) t p_e q_e q0_e a) ^ 2
  let M : RegCoeffField d → ℝ := fun a =>
    σ *
        (WeakNormsMaximizer.gradientMismatchTermAtScale
          (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
      σ⁻¹ *
        (WeakNormsMaximizer.fluxMismatchTermAtScale
          (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2
  let L : RegCoeffField d → ℝ := fun a =>
    σ *
        (WeakNormsMaximizer.gradientLowScaleTailAtScale
          (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
      σ⁻¹ *
        (WeakNormsMaximizer.fluxLowScaleTailAtScale
          (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2
  let T : ℝ :=
    σ *
        (WeakNormsMaximizer.gradientConstantTailAtScale
          (m : ℤ) (k : ℤ) s p0_e) ^ 2 +
      σ⁻¹ *
        (WeakNormsMaximizer.fluxConstantTailAtScale
          (m : ℤ) (k : ℤ) t q0_e) ^ 2
  let W : RegCoeffField d → ℝ := fun a =>
    σ * (gradWeak a) ^ 2 + σ⁻¹ * (fluxWeak a) ^ 2
  let Z : RegCoeffField d → ℝ := fun a =>
    16 * (((H a + K ^ 2 * M a) + K ^ 2 * L a) + K ^ 2 * T)
  have hσ_nonneg : 0 ≤ σ := by
    exact Real.sqrt_nonneg _
  have hGradWeakSqInt :
      Integrable (fun a : RegCoeffField d => (gradWeak a) ^ 2) P := by
    simpa [gradWeak, Q, s, p_e, q_e, p0_e, β] using hGradSq
  have hFluxWeakSqInt :
      Integrable (fun a : RegCoeffField d => (fluxWeak a) ^ 2) P := by
    simpa [fluxWeak, Q, t, p_e, q_e, q0_e, β] using hFluxSq
  have hWInt : Integrable W P := by
    have hG : Integrable (fun a : RegCoeffField d => σ * (gradWeak a) ^ 2) P :=
      hGradWeakSqInt.const_mul σ
    have hF : Integrable (fun a : RegCoeffField d => σ⁻¹ * (fluxWeak a) ^ 2) P :=
      hFluxWeakSqInt.const_mul σ⁻¹
    simpa [W] using! hG.add hF
  have hHigh := integral_paired_highScaleAverageTerms_special_le_fullBlockSumAtScale
      hP hstat hStruct hP4 hkm e he
  rcases integral_paired_mismatchTermSquares_special_le_coarseFluctuationTerms_uniform
      hP4.params with ⟨Cmis, hCmis_nonneg, hMis_all⟩
  have hMis := hMis_all hP hstat hStruct hP4 rfl hkm e
  have hLowRaw :=
    integral_paired_lowScaleTailSquares_special_le_rawLowScaleTerms
      hP hstat hStruct hP4 hkm e
  have hHInt : Integrable H P := by
    simpa [H, β, s, t, p_e, q_e, p0_e, q0_e, σ] using hHigh.1
  have hMInt : Integrable M P := by
    simpa [M, β, s, s', t, t', p_e, q_e, σ] using hMis.1
  have hLInt : Integrable L P := by
    simpa [L, β, s, s', t, t', p_e, q_e, σ] using hLowRaw.1
  have hZInt : Integrable Z P := by
    have hinside :
        Integrable (fun a : RegCoeffField d =>
          ((H a + K ^ 2 * M a) + K ^ 2 * L a) + K ^ 2 * T) P :=
      ((hHInt.add (hMInt.const_mul (K ^ 2))).add
        (hLInt.const_mul (K ^ 2))).add (integrable_const (K ^ 2 * T))
    simpa [Z, mul_assoc] using hinside.const_mul 16
  have hPoint : W ≤ᵐ[P] Z := by
    filter_upwards [ae_paired_weakNormSquares_special_le_four_rhsSquares
      hP hStruct hP4 hkm e] with a hweak
    have hAlg :=
      paired_rhsSquares_le_componentSquares
        (σ := σ) (K := K)
        (AG := WeakNormsMaximizer.gradientAverageTermAtScale
          (m : ℤ) (k : ℤ) s p_e q_e p0_e a)
        (MG := WeakNormsMaximizer.gradientMismatchTermAtScale
          (m : ℤ) (k : ℤ) s s' p_e q_e a)
        (LG := WeakNormsMaximizer.gradientLowScaleTailAtScale
          (m : ℤ) (k : ℤ) s s' p_e q_e a)
        (CG := WeakNormsMaximizer.gradientConstantTailAtScale
          (m : ℤ) (k : ℤ) s p0_e)
        (AF := WeakNormsMaximizer.fluxAverageTermAtScale
          (m : ℤ) (k : ℤ) t p_e q_e q0_e a)
        (MF := WeakNormsMaximizer.fluxMismatchTermAtScale
          (m : ℤ) (k : ℤ) t t' p_e q_e a)
        (LF := WeakNormsMaximizer.fluxLowScaleTailAtScale
          (m : ℤ) (k : ℤ) t t' p_e q_e a)
        (CF := WeakNormsMaximizer.fluxConstantTailAtScale
          (m : ℤ) (k : ℤ) t q0_e) hσ_nonneg
    calc
      W a ≤
          4 *
            (σ *
                (WeakNormsMaximizer.gradientRHSAtScale K
                  (m : ℤ) (k : ℤ) s s' p_e q_e p0_e a) ^ 2 +
              σ⁻¹ *
                (WeakNormsMaximizer.fluxRHSAtScale K
                  (m : ℤ) (k : ℤ) t t' p_e q_e q0_e a) ^ 2) := by
          simpa [W, gradWeak, fluxWeak, K, Q, β, s, s', t, t',
            p_e, q_e, p0_e, q0_e, σ] using hweak
      _ ≤ Z a := by
          dsimp [Z, H, M, L, T, WeakNormsMaximizer.gradientRHSAtScale,
            WeakNormsMaximizer.fluxRHSAtScale]
          nlinarith [hAlg]
  have hmono : ∫ a, W a ∂P ≤ ∫ a, Z a ∂P :=
    integral_mono_ae hWInt hZInt hPoint
  have hZeq :
      ∫ a, Z a ∂P =
        16 *
          ((∫ a, H a ∂P) +
            K ^ 2 * (∫ a, M a ∂P) +
              K ^ 2 * (∫ a, L a ∂P) +
                K ^ 2 * T) := by
    let HM : RegCoeffField d → ℝ := fun a => H a + K ^ 2 * M a
    let HML : RegCoeffField d → ℝ := fun a => HM a + K ^ 2 * L a
    let TC : RegCoeffField d → ℝ := fun _ => K ^ 2 * T
    have hHMInt : Integrable HM P := by
      simpa [HM] using! hHInt.add (hMInt.const_mul (K ^ 2))
    have hHMLInt : Integrable HML P := by
      simpa [HML] using! hHMInt.add (hLInt.const_mul (K ^ 2))
    have hTCInt : Integrable TC P := by
      simpa [TC] using integrable_const (K ^ 2 * T : ℝ)
    have hBody :
        ∫ a, ((H a + K ^ 2 * M a) + K ^ 2 * L a) + K ^ 2 * T ∂P =
          (∫ a, H a ∂P) +
            K ^ 2 * (∫ a, M a ∂P) +
              K ^ 2 * (∫ a, L a ∂P) +
                K ^ 2 * T := by
      calc
        ∫ a, ((H a + K ^ 2 * M a) + K ^ 2 * L a) + K ^ 2 * T ∂P
            = ∫ a, HML a + TC a ∂P := by
                simp [HML, HM, TC]
        _ = ∫ a, HML a ∂P + ∫ a, TC a ∂P := by
                rw [integral_add hHMLInt hTCInt]
        _ = (∫ a, HM a ∂P + ∫ a, K ^ 2 * L a ∂P) +
              ∫ a, TC a ∂P := by
                rw [integral_add hHMInt (hLInt.const_mul (K ^ 2))]
        _ = ((∫ a, H a ∂P + ∫ a, K ^ 2 * M a ∂P) +
              ∫ a, K ^ 2 * L a ∂P) +
              ∫ a, TC a ∂P := by
                rw [integral_add hHInt (hMInt.const_mul (K ^ 2))]
        _ =
          (∫ a, H a ∂P) +
            K ^ 2 * (∫ a, M a ∂P) +
              K ^ 2 * (∫ a, L a ∂P) +
                K ^ 2 * T := by
                rw [integral_const_mul, integral_const_mul, integral_const]
                simp
    calc
      ∫ a, Z a ∂P =
          16 * ∫ a, ((H a + K ^ 2 * M a) + K ^ 2 * L a) + K ^ 2 * T ∂P := by
            rw [integral_const_mul]
      _ =
          16 *
            ((∫ a, H a ∂P) +
              K ^ 2 * (∫ a, M a ∂P) +
                K ^ 2 * (∫ a, L a ∂P) +
                  K ^ 2 * T) := by
            rw [hBody]
  calc
    σ * (∫ a, (gradWeak a) ^ 2 ∂P) +
        σ⁻¹ * (∫ a, (fluxWeak a) ^ 2 ∂P)
        = ∫ a, W a ∂P := by
          have hG : Integrable (fun a : RegCoeffField d => σ * (gradWeak a) ^ 2) P :=
            hGradWeakSqInt.const_mul σ
          have hF : Integrable (fun a : RegCoeffField d => σ⁻¹ * (fluxWeak a) ^ 2) P :=
            hFluxWeakSqInt.const_mul σ⁻¹
          rw [integral_add hG hF, integral_const_mul, integral_const_mul]
    _ ≤ ∫ a, Z a ∂P := hmono
    _ =
        16 *
          ((∫ a, H a ∂P) +
            K ^ 2 * (∫ a, M a ∂P) +
              K ^ 2 * (∫ a, L a ∂P) +
                K ^ 2 * T) := hZeq
    _ =
        16 *
          ((∫ a,
              (σ *
                  (WeakNormsMaximizer.gradientAverageTermAtScale
                    (m : ℤ) (k : ℤ) s p_e q_e p0_e a) ^ 2 +
                σ⁻¹ *
                  (WeakNormsMaximizer.fluxAverageTermAtScale
                    (m : ℤ) (k : ℤ) t p_e q_e q0_e a) ^ 2) ∂P) +
            K ^ 2 *
              (∫ a,
                (σ *
                    (WeakNormsMaximizer.gradientMismatchTermAtScale
                      (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
                  σ⁻¹ *
                    (WeakNormsMaximizer.fluxMismatchTermAtScale
                      (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) ∂P) +
            K ^ 2 *
              (∫ a,
                (σ *
                    (WeakNormsMaximizer.gradientLowScaleTailAtScale
                      (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
                  σ⁻¹ *
                    (WeakNormsMaximizer.fluxLowScaleTailAtScale
                      (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) ∂P) +
            K ^ 2 *
              (σ *
                  (WeakNormsMaximizer.gradientConstantTailAtScale
                    (m : ℤ) (k : ℤ) s p0_e) ^ 2 +
                σ⁻¹ *
                  (WeakNormsMaximizer.fluxConstantTailAtScale
                    (m : ℤ) (k : ℤ) t q0_e) ^ 2)) := by
          simp [H, M, L, T]

/-- The paired special-vector weak-norm square expectations are bounded by the
four square-conversion terms of the manuscript coarse-fluctuation RHS. -/
theorem paired_weakNormSquares_special_le_coarseFluctuationTerms
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P) (_hstat : Ch04.RestrictionStationaryLaw P)
      (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      ∀ {k m : ℕ}, k < m → ∀ e : Vec d, vecNormSq e = 1 →
      (let β := section53CoarseFluctuationBeta hP4
       let s := hP4.sLower + 2 * β
       let p_e := specialPAtScale hP hStruct (m : ℤ) e
       let q_e := specialQAtScale hP hStruct (m : ℤ) e
       let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
       Integrable
         (fun a : RegCoeffField d =>
           (Ch04.canonicalScalarResponseGradientWeakNormCubeSet
               (originCube d (m : ℤ)) s p_e q_e p0_e a.toFun) ^ 2) P) →
      (let β := section53CoarseFluctuationBeta hP4
       let t := hP4.sUpper + 2 * β
       let p_e := specialPAtScale hP hStruct (m : ℤ) e
       let q_e := specialQAtScale hP hStruct (m : ℤ) e
       let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
       Integrable
         (fun a : RegCoeffField d =>
           (Ch04.canonicalScalarResponseFluxWeakNormCubeSet
               (originCube d (m : ℤ)) t p_e q_e q0_e a.toFun) ^ 2) P) →
        let β := section53CoarseFluctuationBeta hP4
        let s := hP4.sLower + 2 * β
        let t := hP4.sUpper + 2 * β
        let Q : TriadicCube d := originCube d (m : ℤ)
        let p_e := specialPAtScale hP hStruct (m : ℤ) e
        let q_e := specialQAtScale hP hStruct (m : ℤ) e
        let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
        let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
        let σ := sigmaHatAtScale hP hStruct (m : ℤ)
        let θ := thetaAtScale hP hStruct (m : ℤ)
        let gradWeak :=
          Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p_e q_e p0_e
        let fluxWeak :=
          Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p_e q_e q0_e
        σ * (∫ a, (gradWeak a) ^ 2 ∂P) +
            σ⁻¹ * (∫ a, (fluxWeak a) ^ 2 ∂P)
          ≤
            C *
              (β⁻¹ * θ *
                  coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m +
                (β ^ 2)⁻¹ *
                  coarseFluctuationScalarWeightAtScale hP hStruct m *
                    coarseFluctuationTauSumAtScale hP hStruct hP4 k m e +
                (hP4.xi : ℝ) * (β ^ 3)⁻¹ *
                  Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
                  coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
                    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e +
                (β ^ 2)⁻¹ *
                  Real.rpow (3 : ℝ)
                    (-2 * β * (((m - k : ℕ) : ℝ))) *
                  coarseFluctuationScalarWeightAtScale hP hStruct m *
                    (θ - 1)) := by
  classical
  dsimp only
  let K := WeakNormsMaximizer.section53WeakNormMaximizerConst d
  rcases integral_paired_highScaleAverageTerms_special_le_beta_inv_fullBlockSumAtScale
      (d := d) with ⟨CH, hCH_nonneg, hH_all⟩
  rcases integral_paired_mismatchTermSquares_special_le_coarseFluctuationTerms_uniform
      params with ⟨CM, hCM_nonneg, hM_all⟩
  rcases integral_paired_lowScaleTailSquares_special_le_coarseFluctuationTerms_uniform
      params with ⟨CL, hCL_nonneg, hL_all⟩
  let C0 : ℝ := CH + K ^ 2 * CM + K ^ 2 * CL + 2 * K ^ 2
  let C : ℝ := 16 * C0
  have hC0_nonneg : 0 ≤ C0 := by
    simpa [C0] using pairedConstant_nonneg (K := K) hCH_nonneg hCM_nonneg hCL_nonneg
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by norm_num) hC0_nonneg
  refine ⟨C, hC_nonneg, ?_⟩
  intro P hP hstat hStruct hP4 hparams k m hkm e he hGradSq hFluxSq
  let : IsProbabilityMeasure P := hP.isProbability
  subst params
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let s' := hP4.sLower + β
  let t := hP4.sUpper + 2 * β
  let t' := hP4.sUpper + β
  let Q : TriadicCube d := originCube d (m : ℤ)
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let θ := thetaAtScale hP hStruct (m : ℤ)
  let gradWeak :=
    Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p_e q_e p0_e
  let fluxWeak :=
    Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p_e q_e q0_e
  let H : ℝ :=
    ∫ a,
      (σ *
          (WeakNormsMaximizer.gradientAverageTermAtScale
            (m : ℤ) (k : ℤ) s p_e q_e p0_e a) ^ 2 +
        σ⁻¹ *
          (WeakNormsMaximizer.fluxAverageTermAtScale
            (m : ℤ) (k : ℤ) t p_e q_e q0_e a) ^ 2) ∂P
  let M : ℝ :=
    ∫ a,
      (σ *
          (WeakNormsMaximizer.gradientMismatchTermAtScale
            (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
        σ⁻¹ *
          (WeakNormsMaximizer.fluxMismatchTermAtScale
            (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) ∂P
  let L : ℝ :=
    ∫ a,
      (σ *
          (WeakNormsMaximizer.gradientLowScaleTailAtScale
            (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
        σ⁻¹ *
          (WeakNormsMaximizer.fluxLowScaleTailAtScale
            (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) ∂P
  let T : ℝ :=
    σ *
        (WeakNormsMaximizer.gradientConstantTailAtScale
          (m : ℤ) (k : ℤ) s p0_e) ^ 2 +
      σ⁻¹ *
        (WeakNormsMaximizer.fluxConstantTailAtScale
          (m : ℤ) (k : ℤ) t q0_e) ^ 2
  let A : ℝ :=
    β⁻¹ * θ *
      coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m
  let B : ℝ :=
    (β ^ 2)⁻¹ * coarseFluctuationScalarWeightAtScale hP hStruct m *
      coarseFluctuationTauSumAtScale hP hStruct hP4 k m e
  let R : ℝ :=
    (hP4.xi : ℝ) * (β ^ 3)⁻¹ *
      Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
      coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
        coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
  let D : ℝ :=
    (β ^ 2)⁻¹ *
      Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) *
      coarseFluctuationScalarWeightAtScale hP hStruct m * (θ - 1)
  let Ssum : ℝ := A + B + R + D
  have hcomp :=
    paired_weakNormSquares_special_le_componentIntegrals
      hP hstat hStruct hP4 hkm e he hGradSq hFluxSq
  have hH := hH_all hP hstat hStruct hP4 hkm e he
  have hM := hM_all hP hstat hStruct hP4 rfl hkm e
  have hL := hL_all hP hstat hStruct hP4 rfl hkm e he
  have hT :=
    paired_constantTail_special_le_lowScaleTail hP hStruct hP4 hkm e he
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg (inv_nonneg.mpr hβ_pos.le)
        (by
          have hθ : 1 ≤ θ := by
            simpa [θ] using one_le_thetaAtScale_of_P4 hP hStruct hP4 m
          linarith))
      (coarseFluctuationFullBlockSumAtScale_nonneg hP hStruct hP4 k m)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg (inv_nonneg.mpr (sq_nonneg _))
        (coarseFluctuationScalarWeightAtScale_nonneg hP hStruct hP4 m))
      (coarseFluctuationTauSumAtScale_nonneg hP hstat hStruct hP4 k m e)
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by exact_mod_cast Nat.zero_le hP4.xi)
            (inv_nonneg.mpr (pow_nonneg hβ_pos.le 3)))
          (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
        (coarseFluctuationUnitMomentWeightAtScale_nonneg hP hStruct hP4 m))
      (coarseFluctuationResponseMomentAtScale_nonneg hP hStruct hP4 k m e)
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (inv_nonneg.mpr (sq_nonneg _))
          (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
        (coarseFluctuationScalarWeightAtScale_nonneg hP hStruct hP4 m))
      (by
        have hθ : 1 ≤ θ := by
          simpa [θ] using one_le_thetaAtScale_of_P4 hP hStruct hP4 m
        linarith)
  have hS_nonneg : 0 ≤ Ssum := by
    simpa [Ssum] using rhsSum_nonneg hA_nonneg hB_nonneg hR_nonneg hD_nonneg
  have hA_le_Ssum : A ≤ Ssum := by
    simpa [Ssum] using first_le_rhsSum hB_nonneg hR_nonneg hD_nonneg
  have hBR_le_Ssum : B + R ≤ Ssum := by
    simpa [Ssum] using middle_pair_le_rhsSum hA_nonneg hD_nonneg
  have hDR_le_Ssum : D + R ≤ Ssum := by
    simpa [Ssum] using last_pair_le_rhsSum hA_nonneg hB_nonneg
  have hD_le_Ssum : D ≤ Ssum := by
    simpa [Ssum] using fourth_le_rhsSum (D := D) hA_nonneg hB_nonneg hR_nonneg
  have hH_le : H ≤ CH * Ssum := by
    have hHA' :
        H ≤ CH * β⁻¹ * θ *
          coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m := by
      simpa [H, β, s, t, p_e, q_e, p0_e, q0_e, σ, θ] using hH
    have hHA : H ≤ CH * A := by
      calc
        H ≤ CH * β⁻¹ * θ *
            coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m := hHA'
        _ = CH * A := by
            simp [A]
            ring
    calc
      H ≤ CH * A := hHA
      _ ≤ CH * Ssum := by
        exact mul_le_mul_of_nonneg_left hA_le_Ssum hCH_nonneg
  have hM_le : M ≤ CM * Ssum := by
    have hMBR : M ≤ CM * (B + R) := by
      simpa [M, B, R, β, s, s', t, t', p_e, q_e, σ] using hM.2
    calc
      M ≤ CM * (B + R) := hMBR
      _ ≤ CM * Ssum := by
        exact mul_le_mul_of_nonneg_left hBR_le_Ssum hCM_nonneg
  have hL_le : L ≤ CL * Ssum := by
    have hLDR : L ≤ CL * (D + R) := by
      simpa [L, D, R, β, s, s', t, t', p_e, q_e, σ, θ] using hL
    calc
      L ≤ CL * (D + R) := hLDR
      _ ≤ CL * Ssum := by
        exact mul_le_mul_of_nonneg_left hDR_le_Ssum hCL_nonneg
  have hT_le : T ≤ 2 * Ssum := by
    have hTD : T ≤ 2 * D := by
      simpa [T, D, β, s, t, p_e, q_e, p0_e, q0_e, σ, θ] using hT
    calc
      T ≤ 2 * D := hTD
      _ ≤ 2 * Ssum := by
        exact mul_le_mul_of_nonneg_left hD_le_Ssum (by norm_num)
  have hinside :
      H + K ^ 2 * M + K ^ 2 * L + K ^ 2 * T ≤ C0 * Ssum := by
    exact pairedComponentSum_le hH_le hM_le hL_le hT_le (sq_nonneg K) (by rfl)
  calc
    σ * (∫ a, (gradWeak a) ^ 2 ∂P) +
        σ⁻¹ * (∫ a, (fluxWeak a) ^ 2 ∂P)
        ≤ 16 * (H + K ^ 2 * M + K ^ 2 * L + K ^ 2 * T) := by
          simpa [H, M, L, T, K, β, s, s', t, t', Q, p_e, q_e, p0_e,
            q0_e, σ, gradWeak, fluxWeak] using hcomp
    _ ≤ 16 * (C0 * Ssum) :=
          mul_le_mul_of_nonneg_left hinside (by norm_num)
    _ =
        C *
          (β⁻¹ * θ *
              coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m +
            (β ^ 2)⁻¹ *
              coarseFluctuationScalarWeightAtScale hP hStruct m *
                coarseFluctuationTauSumAtScale hP hStruct hP4 k m e +
            (hP4.xi : ℝ) * (β ^ 3)⁻¹ *
              Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
              coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
                coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e +
            (β ^ 2)⁻¹ *
              Real.rpow (3 : ℝ)
                (-2 * β * (((m - k : ℕ) : ℝ))) *
              coarseFluctuationScalarWeightAtScale hP hStruct m * (θ - 1)) := by
        simp [C, Ssum, A, B, R, D]
        ring

end

end JUpperBoundCoarseFluctuations
end Section53
end Ch05
end Book
end Homogenization
