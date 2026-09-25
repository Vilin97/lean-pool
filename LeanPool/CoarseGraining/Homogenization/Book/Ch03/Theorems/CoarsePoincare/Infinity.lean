/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarsePoincare.Finite
public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Definitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.Existence
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincare.QTwo
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfaces.AECongruence

/-! # Infinity -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Section 3.1.1: Coarse Poincare infinity-depth estimates

This file contains the infinity-depth scalar algebra and series identities used
by the public coarse Poincare theorem package.
-/

noncomputable section

open scoped BigOperators

theorem multiscaleDescendantWeight_sub_nat {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (j : ℕ) :
    Ch02.multiscaleDescendantWeight Q (Q.scale - (j : ℤ)) s =
      Real.rpow (3 : ℝ) (2 * s * (j : ℝ)) := by
  unfold Ch02.multiscaleDescendantWeight
  have hsub : Q.scale - (Q.scale - (j : ℤ)) = (j : ℤ) := by
    abel
  rw [hsub]
  norm_num

theorem rpow_inv_half_eq_rpow_neg_half {x : ℝ} (hx : 0 ≤ x) :
    Real.rpow x⁻¹ (1 / 2 : ℝ) = Real.rpow x (-(1 / 2 : ℝ)) := by
  have hinv_eq : x⁻¹ = Real.rpow x (-1 : ℝ) :=
    (Real.rpow_neg_one x).symm
  calc
    Real.rpow x⁻¹ (1 / 2 : ℝ) =
        Real.rpow (Real.rpow x (-1 : ℝ)) (1 / 2 : ℝ) := by
          rw [hinv_eq]
    _ = Real.rpow x ((-1 : ℝ) * (1 / 2 : ℝ)) := by
          exact (Real.rpow_mul hx (-1 : ℝ) (1 / 2 : ℝ)).symm
    _ = Real.rpow x (-(1 / 2 : ℝ)) := by
          ring_nf

theorem rpow_depth_weight_sqrt_cancel
    {s : ℝ} (j : ℕ) {L E : ℝ} (hL : 0 ≤ L) (hE : 0 ≤ E) :
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        Real.sqrt ((Real.rpow (3 : ℝ) (2 * s * (j : ℝ)) * L) * E) =
      Real.rpow L (1 / 2 : ℝ) * Real.sqrt E := by
  have h3nonneg : 0 ≤ (3 : ℝ) := by norm_num
  have h3pos : 0 < (3 : ℝ) := by norm_num
  have hA_nonneg :
      0 ≤ Real.rpow (3 : ℝ) (2 * s * (j : ℝ)) :=
    Real.rpow_nonneg h3nonneg _
  have hLE_nonneg : 0 ≤ L * E := mul_nonneg hL hE
  have hsqrt_weight :
      Real.sqrt (Real.rpow (3 : ℝ) (2 * s * (j : ℝ))) =
        Real.rpow (3 : ℝ) (s * (j : ℝ)) := by
    calc
      Real.sqrt (Real.rpow (3 : ℝ) (2 * s * (j : ℝ))) =
          Real.rpow (Real.rpow (3 : ℝ) (2 * s * (j : ℝ))) (1 / 2 : ℝ) := by
            exact Real.sqrt_eq_rpow _
      _ = Real.rpow (3 : ℝ) ((2 * s * (j : ℝ)) * (1 / 2 : ℝ)) := by
            exact (Real.rpow_mul h3nonneg (2 * s * (j : ℝ)) (1 / 2 : ℝ)).symm
      _ = Real.rpow (3 : ℝ) (s * (j : ℝ)) := by
            congr 1
            ring
  have hcancel :
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          Real.rpow (3 : ℝ) (s * (j : ℝ)) = 1 := by
    calc
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          Real.rpow (3 : ℝ) (s * (j : ℝ)) =
        Real.rpow (3 : ℝ) (-s * (j : ℝ) + s * (j : ℝ)) := by
          exact (Real.rpow_add h3pos (-s * (j : ℝ)) (s * (j : ℝ))).symm
      _ = 1 := by
          rw [show -s * (j : ℝ) + s * (j : ℝ) = 0 by ring]
          exact Real.rpow_zero (3 : ℝ)
  calc
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        Real.sqrt ((Real.rpow (3 : ℝ) (2 * s * (j : ℝ)) * L) * E)
        =
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        Real.sqrt (Real.rpow (3 : ℝ) (2 * s * (j : ℝ)) * (L * E)) := by
        rw [mul_assoc]
    _ =
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        (Real.sqrt (Real.rpow (3 : ℝ) (2 * s * (j : ℝ))) *
          Real.sqrt (L * E)) := by
        rw [Real.sqrt_mul hA_nonneg]
    _ =
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          (Real.sqrt L * Real.sqrt E)) := by
        rw [hsqrt_weight, Real.sqrt_mul hL]
    _ =
      (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          Real.rpow (3 : ℝ) (s * (j : ℝ))) *
        (Real.sqrt L * Real.sqrt E) := by
        ring
    _ = Real.rpow L (1 / 2 : ℝ) * Real.sqrt E := by
        rw [hcancel, Real.sqrt_eq_rpow L]
        simp

theorem infinity_gradient_norm_le_of_cubeAverageEnergyControl {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffFamily d)
    (s : ℝ) (hs : 0 < s)
    (F : Vec d → Vec d) (energy : Vec d → ℝ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (hdepthAverage :
      ∀ n : ℕ,
        negativeBesovVectorDepthAverage Q F n ≤
          Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a *
            cubeAverage Q energy) :
    scaleNormalizedNegativeBesovVectorNorm Q s .infinity F ≤
      poincareDiscountFactor s .infinity *
        poincareLowerEllipticityFactor Q a s .infinity *
          Real.sqrt (cubeAverage Q energy) := by
  let E : ℝ := cubeAverage Q energy
  let M : ℕ → ℝ := fun n =>
    Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a
  let lam : ℝ := Ch02.lambdaSq Q s .infinity a
  have hE_nonneg : 0 ≤ E := by
    exact cubeAverage_nonneg_of_nonneg_on henergy_nonneg
  have hlam_pos : 0 < lam := by
    dsimp [lam]
    exact Ch02.lambdaSq_infinity_pos Q a hs
  have hlam_inv_nonneg : 0 ≤ lam⁻¹ := inv_nonneg.mpr hlam_pos.le
  have hdepth :
      ∀ j : ℕ,
        negativeBesovVectorDepthSeminorm Q s F j ≤
          Real.rpow lam (-(1 / 2 : ℝ)) * Real.sqrt E := by
    intro j
    have havg :
        negativeBesovVectorDepthAverage Q F j ≤ M j * E := by
      simpa [M, E] using hdepthAverage j
    have hk : Q.scale - (j : ℤ) ≤ Q.scale :=
      sub_le_self _ (by exact_mod_cast Nat.zero_le j)
    have hM_bound :
        M j ≤ Real.rpow (3 : ℝ) (2 * s * (j : ℝ)) * lam⁻¹ := by
      have h1 :
          M j ≤
            Ch02.maxDescendantLowerEllipticityInvAtScale Q (Q.scale - (j : ℤ))
              s .infinity a := by
        dsimp [M]
        exact Ch02.maxDescendant_sigmaStarInv_le_maxDescendant_lambdaSq_inv
          Q a hk hs Ch02.MultiscaleExponent.isAdmissible_infinity
      have h2 :
          Ch02.maxDescendantLowerEllipticityInvAtScale Q (Q.scale - (j : ℤ))
              s .infinity a ≤
            Ch02.multiscaleDescendantWeight Q (Q.scale - (j : ℤ)) s *
              (Ch02.lambdaSq Q s .infinity a)⁻¹ :=
        Ch02.maxDescendant_lambdaSq_inv_le
          Q a hk hs Ch02.MultiscaleExponent.isAdmissible_infinity
      calc
        M j ≤
            Ch02.maxDescendantLowerEllipticityInvAtScale Q (Q.scale - (j : ℤ))
              s .infinity a := h1
        _ ≤ Ch02.multiscaleDescendantWeight Q (Q.scale - (j : ℤ)) s *
              (Ch02.lambdaSq Q s .infinity a)⁻¹ := h2
        _ = Real.rpow (3 : ℝ) (2 * s * (j : ℝ)) * lam⁻¹ := by
              rw [multiscaleDescendantWeight_sub_nat]
    have hME_bound :
        M j * E ≤
          (Real.rpow (3 : ℝ) (2 * s * (j : ℝ)) * lam⁻¹) * E :=
      mul_le_mul_of_nonneg_right hM_bound hE_nonneg
    have htarget_nonneg :
        0 ≤ (Real.rpow (3 : ℝ) (2 * s * (j : ℝ)) * lam⁻¹) * E := by
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _) hlam_inv_nonneg)
        hE_nonneg
    have hweight_nonneg :
        0 ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) :=
      Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
    calc
      negativeBesovVectorDepthSeminorm Q s F j
          ≤
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          Real.sqrt (M j * E) := by
          unfold negativeBesovVectorDepthSeminorm
          exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt havg) hweight_nonneg
      _ ≤
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          Real.sqrt ((Real.rpow (3 : ℝ) (2 * s * (j : ℝ)) * lam⁻¹) * E) := by
          exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hME_bound) hweight_nonneg
      _ = Real.rpow lam (-(1 / 2 : ℝ)) * Real.sqrt E := by
          rw [rpow_depth_weight_sqrt_cancel j hlam_inv_nonneg hE_nonneg]
          rw [rpow_inv_half_eq_rpow_neg_half hlam_pos.le]
  calc
    scaleNormalizedNegativeBesovVectorNorm Q s .infinity F
        ≤ Real.rpow lam (-(1 / 2 : ℝ)) * Real.sqrt E :=
      scaleNormalizedNegativeBesovVectorNorm_infinity_le_of_depthBound Q s F hdepth
    _ =
      poincareDiscountFactor s .infinity *
        poincareLowerEllipticityFactor Q a s .infinity *
          Real.sqrt E := by
      simp [poincareDiscountFactor, poincareLowerEllipticityFactor, lam]

theorem infinity_flux_norm_le_of_cubeAverageEnergyControl {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffFamily d)
    (s : ℝ) (hs : 0 < s)
    (F : Vec d → Vec d) (energy : Vec d → ℝ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (hdepthAverage :
      ∀ n : ℕ,
        negativeBesovVectorDepthAverage Q F n ≤
          Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a *
            cubeAverage Q energy) :
    scaleNormalizedNegativeBesovVectorNorm Q s .infinity F ≤
      poincareDiscountFactor s .infinity *
        poincareUpperEllipticityFactor Q a s .infinity *
          Real.sqrt (cubeAverage Q energy) := by
  let E : ℝ := cubeAverage Q energy
  let M : ℕ → ℝ := fun n =>
    Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a
  let Lam : ℝ := Ch02.LambdaSq Q s .infinity a
  have hE_nonneg : 0 ≤ E := by
    exact cubeAverage_nonneg_of_nonneg_on henergy_nonneg
  have hLam_nonneg : 0 ≤ Lam := by
    dsimp [Lam]
    exact Ch02.LambdaSq_infinity_nonneg Q a hs
  have hdepth :
      ∀ j : ℕ,
        negativeBesovVectorDepthSeminorm Q s F j ≤
          Real.rpow Lam (1 / 2 : ℝ) * Real.sqrt E := by
    intro j
    have havg :
        negativeBesovVectorDepthAverage Q F j ≤ M j * E := by
      simpa [M, E] using hdepthAverage j
    have hk : Q.scale - (j : ℤ) ≤ Q.scale :=
      sub_le_self _ (by exact_mod_cast Nat.zero_le j)
    have hM_bound :
        M j ≤ Real.rpow (3 : ℝ) (2 * s * (j : ℝ)) * Lam := by
      have h1 :
          M j ≤
            Ch02.maxDescendantUpperEllipticityAtScale Q (Q.scale - (j : ℤ))
              s .infinity a := by
        dsimp [M]
        exact Ch02.maxDescendant_b_le_maxDescendant_LambdaSq
          Q a hk hs Ch02.MultiscaleExponent.isAdmissible_infinity
      have h2 :
          Ch02.maxDescendantUpperEllipticityAtScale Q (Q.scale - (j : ℤ))
              s .infinity a ≤
            Ch02.multiscaleDescendantWeight Q (Q.scale - (j : ℤ)) s *
              Ch02.LambdaSq Q s .infinity a :=
        Ch02.maxDescendant_LambdaSq_le
          Q a hk hs Ch02.MultiscaleExponent.isAdmissible_infinity
      calc
        M j ≤
            Ch02.maxDescendantUpperEllipticityAtScale Q (Q.scale - (j : ℤ))
              s .infinity a := h1
        _ ≤ Ch02.multiscaleDescendantWeight Q (Q.scale - (j : ℤ)) s *
              Ch02.LambdaSq Q s .infinity a := h2
        _ = Real.rpow (3 : ℝ) (2 * s * (j : ℝ)) * Lam := by
              rw [multiscaleDescendantWeight_sub_nat]
    have hME_bound :
        M j * E ≤
          (Real.rpow (3 : ℝ) (2 * s * (j : ℝ)) * Lam) * E :=
      mul_le_mul_of_nonneg_right hM_bound hE_nonneg
    have hweight_nonneg :
        0 ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) :=
      Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
    calc
      negativeBesovVectorDepthSeminorm Q s F j
          ≤
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          Real.sqrt (M j * E) := by
          unfold negativeBesovVectorDepthSeminorm
          exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt havg) hweight_nonneg
      _ ≤
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          Real.sqrt ((Real.rpow (3 : ℝ) (2 * s * (j : ℝ)) * Lam) * E) := by
          exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hME_bound) hweight_nonneg
      _ = Real.rpow Lam (1 / 2 : ℝ) * Real.sqrt E := by
          rw [rpow_depth_weight_sqrt_cancel j hLam_nonneg hE_nonneg]
  calc
    scaleNormalizedNegativeBesovVectorNorm Q s .infinity F
        ≤ Real.rpow Lam (1 / 2 : ℝ) * Real.sqrt E :=
      scaleNormalizedNegativeBesovVectorNorm_infinity_le_of_depthBound Q s F hdepth
    _ =
      poincareDiscountFactor s .infinity *
        poincareUpperEllipticityFactor Q a s .infinity *
          Real.sqrt E := by
      simp [poincareDiscountFactor, poincareUpperEllipticityFactor, Lam]

theorem summable_public_sigmaStar_series {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffFamily d) {s q : ℝ}
    (hs : 0 < s) (hq : 0 < q) :
    Summable fun n : ℕ =>
      Ch02.geometricWeight s q n *
        Real.rpow
          (Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
          (q / 2) := by
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain Q) (a.coeffOn Q)
  have hOld :=
    Ch02.summable_sigmaStarInv_series_pointwiseCoeffField
      (Q := Q) (a := a) hs hq
  simpa [A] using hOld

theorem summable_public_B_series {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffFamily d) {s q : ℝ}
    (hs : 0 < s) (hq : 0 < q) :
    Summable fun n : ℕ =>
      Ch02.geometricWeight s q n *
        Real.rpow
          (Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
          (q / 2) := by
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain Q) (a.coeffOn Q)
  have hOld :=
    Ch02.summable_B_series_pointwiseCoeffField
      (Q := Q) (a := a) hs hq
  simpa [A] using hOld

theorem tsum_public_sigmaStar_series_eq_lambdaSq {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffFamily d) {s q : ℝ}
    (hs : 0 < s) (hq : 0 < q) :
    (∑' n : ℕ,
      Ch02.geometricWeight s q n *
        Real.rpow
          (Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
          (q / 2)) =
      Real.rpow (Ch02.lambdaSq Q s (.finite q) a) (-q / 2) := by
  exact (Ch02.lambdaSqFinite_rpow_neg_q_div_two_eq_tsum
    Q s q a hq (mul_nonneg hs.le hq.le)).symm

theorem tsum_public_B_series_eq_LambdaSq {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffFamily d) {s q : ℝ}
    (hs : 0 < s) (hq : 0 < q) :
    (∑' n : ℕ,
      Ch02.geometricWeight s q n *
        Real.rpow
          (Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
          (q / 2)) =
      Real.rpow (Ch02.LambdaSq Q s (.finite q) a) (q / 2) := by
  exact (Ch02.LambdaSqFinite_rpow_q_div_two_eq_tsum
    Q s q a hq (mul_nonneg hs.le hq.le)).symm

end

end Ch03
end Book
end Homogenization
