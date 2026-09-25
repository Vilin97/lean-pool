/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarsePoincare.NegativeBesov
public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Definitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.Existence
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincare.QTwo
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfaces.AECongruence

/-! # Finite -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Section 3.1.1: Coarse Poincare finite-depth estimates

This file contains the finite-depth scalar algebra and gradient/flux estimates
used by the public coarse Poincare theorem package.
-/

noncomputable section

open scoped BigOperators

theorem rpow_inv_geometricDiscount_mul_geometricWeight
    {s q : ℝ} (hs : 0 < s) (hq : 0 < q) (j : ℕ) :
    Real.rpow (3 : ℝ) (-s * (j : ℝ) * q) =
      (Ch02.geometricDiscount s q)⁻¹ * Ch02.geometricWeight s q j := by
  have hsq : 0 < s * q := mul_pos hs hq
  have hdisc_pos : 0 < Ch02.geometricDiscount s q := by
    have h := Homogenization.geometricDiscount_pos hsq
    simpa [Ch02.geometricDiscount, Homogenization.geometricDiscount] using h
  have hdisc_ne : Ch02.geometricDiscount s q ≠ 0 := hdisc_pos.ne'
  calc
    Real.rpow (3 : ℝ) (-s * (j : ℝ) * q) =
        (Ch02.geometricDiscount s q)⁻¹ *
          (Ch02.geometricDiscount s q *
            Real.rpow (3 : ℝ) (-s * (j : ℝ) * q)) := by
          field_simp [hdisc_ne]
    _ = (Ch02.geometricDiscount s q)⁻¹ * Ch02.geometricWeight s q j := by
          unfold Ch02.geometricWeight
          congr 1
          congr 1
          ring_nf

private theorem rpow_finite_ellipticity_rhs
    {disc L E q β : ℝ} (hdisc : 0 < disc) (hL : 0 ≤ L)
    (hE : 0 ≤ E) (hq : 0 < q) :
    Real.rpow (disc⁻¹ * Real.rpow L β * Real.rpow E (q / 2)) (1 / q) =
      Real.rpow disc (-(1 / q)) * Real.rpow L (β * (1 / q)) * Real.sqrt E := by
  have hdisc_nonneg : 0 ≤ disc := hdisc.le
  have hdisc_inv_nonneg : 0 ≤ disc⁻¹ := inv_nonneg.mpr hdisc_nonneg
  have hLpow_nonneg : 0 ≤ Real.rpow L β := Real.rpow_nonneg hL _
  have hEpow_nonneg : 0 ≤ Real.rpow E (q / 2) := Real.rpow_nonneg hE _
  have hA :
      Real.rpow disc⁻¹ (1 / q) = Real.rpow disc (-(1 / q)) := by
    have hinv_eq : disc⁻¹ = Real.rpow disc (-1 : ℝ) :=
      (Real.rpow_neg_one disc).symm
    calc
      Real.rpow disc⁻¹ (1 / q) =
          Real.rpow (Real.rpow disc (-1 : ℝ)) (1 / q) := by
            rw [hinv_eq]
      _ = Real.rpow disc ((-1 : ℝ) * (1 / q)) := by
            exact (Real.rpow_mul hdisc_nonneg (-1 : ℝ) (1 / q)).symm
      _ = Real.rpow disc (-(1 / q)) := by ring_nf
  have hB :
      Real.rpow (Real.rpow L β) (1 / q) =
        Real.rpow L (β * (1 / q)) := by
    exact (Real.rpow_mul hL β (1 / q)).symm
  have hC :
      Real.rpow (Real.rpow E (q / 2)) (1 / q) = Real.sqrt E := by
    calc
      Real.rpow (Real.rpow E (q / 2)) (1 / q) =
          Real.rpow E ((q / 2) * (1 / q)) := by
            exact (Real.rpow_mul hE (q / 2) (1 / q)).symm
      _ = Real.rpow E (1 / 2 : ℝ) := by
            field_simp [hq.ne']
      _ = Real.sqrt E := by exact (Real.sqrt_eq_rpow E).symm
  calc
    Real.rpow (disc⁻¹ * Real.rpow L β * Real.rpow E (q / 2)) (1 / q)
        =
          Real.rpow (disc⁻¹ * Real.rpow L β) (1 / q) *
            Real.rpow (Real.rpow E (q / 2)) (1 / q) := by
          exact Real.mul_rpow
            (mul_nonneg hdisc_inv_nonneg hLpow_nonneg) hEpow_nonneg
    _ =
          Real.rpow disc⁻¹ (1 / q) *
            Real.rpow (Real.rpow L β) (1 / q) *
            Real.rpow (Real.rpow E (q / 2)) (1 / q) := by
          have hmul :=
            Real.mul_rpow (x := disc⁻¹) (y := Real.rpow L β)
              (z := 1 / q) hdisc_inv_nonneg hLpow_nonneg
          change (disc⁻¹ * Real.rpow L β) ^ (1 / q) *
              (Real.rpow E (q / 2)) ^ (1 / q) =
            disc⁻¹ ^ (1 / q) *
              (Real.rpow L β) ^ (1 / q) *
                (Real.rpow E (q / 2)) ^ (1 / q)
          rw [hmul]
    _ = Real.rpow disc (-(1 / q)) * Real.rpow L (β * (1 / q)) * Real.sqrt E := by
          rw [hA, hB, hC]

theorem rpow_finite_gradient_rhs
    {disc L E q : ℝ} (hdisc : 0 < disc) (hL : 0 ≤ L)
    (hE : 0 ≤ E) (hq : 0 < q) :
    Real.rpow (disc⁻¹ * Real.rpow L (-q / 2) * Real.rpow E (q / 2)) (1 / q) =
      Real.rpow disc (-(1 / q)) * Real.rpow L (-(1 / 2 : ℝ)) * Real.sqrt E := by
  calc
    Real.rpow (disc⁻¹ * Real.rpow L (-q / 2) * Real.rpow E (q / 2)) (1 / q)
        =
          Real.rpow disc (-(1 / q)) * Real.rpow L ((-q / 2) * (1 / q)) *
            Real.sqrt E := by
          exact rpow_finite_ellipticity_rhs
            (disc := disc) (L := L) (E := E) (q := q) (β := -q / 2)
            hdisc hL hE hq
    _ = Real.rpow disc (-(1 / q)) * Real.rpow L (-(1 / 2 : ℝ)) * Real.sqrt E := by
          rw [show (-q / 2) * (1 / q) = -(1 / 2 : ℝ) by field_simp [hq.ne']]

theorem rpow_finite_flux_rhs
    {disc L E q : ℝ} (hdisc : 0 < disc) (hL : 0 ≤ L)
    (hE : 0 ≤ E) (hq : 0 < q) :
    Real.rpow (disc⁻¹ * Real.rpow L (q / 2) * Real.rpow E (q / 2)) (1 / q) =
      Real.rpow disc (-(1 / q)) * Real.rpow L (1 / 2 : ℝ) * Real.sqrt E := by
  calc
    Real.rpow (disc⁻¹ * Real.rpow L (q / 2) * Real.rpow E (q / 2)) (1 / q)
        =
          Real.rpow disc (-(1 / q)) * Real.rpow L ((q / 2) * (1 / q)) *
            Real.sqrt E := by
          exact rpow_finite_ellipticity_rhs
            (disc := disc) (L := L) (E := E) (q := q) (β := q / 2)
            hdisc hL hE hq
    _ = Real.rpow disc (-(1 / q)) * Real.rpow L (1 / 2 : ℝ) * Real.sqrt E := by
          rw [show (q / 2) * (1 / q) = (1 / 2 : ℝ) by field_simp [hq.ne']]

private theorem finite_norm_le_of_depthAverage_tsum {d : ℕ} [NeZero d]
    (Q : TriadicCube d)
    (s q : ℝ) (hs : 0 < s) (hq : 1 ≤ q)
    (F : Vec d → Vec d) (energy : Vec d → ℝ)
    (M : ℕ → ℝ) (Lpow : ℝ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (hM_nonneg : ∀ n : ℕ, 0 ≤ M n)
    (hdepthAverage :
      ∀ n : ℕ,
        negativeBesovVectorDepthAverage Q F n ≤ M n * cubeAverage Q energy)
    (hsum :
      Summable fun n : ℕ =>
        Ch02.geometricWeight s q n * Real.rpow (M n) (q / 2))
    (htsum :
      (∑' n : ℕ,
        Ch02.geometricWeight s q n * Real.rpow (M n) (q / 2)) = Lpow) :
    scaleNormalizedNegativeBesovVectorNorm Q s (.finite q) F ≤
      Real.rpow
        ((Ch02.geometricDiscount s q)⁻¹ * Lpow *
          Real.rpow (cubeAverage Q energy) (q / 2))
        (1 / q) := by
  let E : ℝ := cubeAverage Q energy
  let W : ℕ → ℝ := fun n =>
    Ch02.geometricWeight s q n * Real.rpow (M n) (q / 2)
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hsq_nonneg : 0 ≤ s * q := mul_nonneg hs.le hqpos.le
  have hdisc_pos : 0 < Ch02.geometricDiscount s q := by
    have h := Homogenization.geometricDiscount_pos (mul_pos hs hqpos)
    simpa [Ch02.geometricDiscount, Homogenization.geometricDiscount] using h
  have hE_nonneg : 0 ≤ E := by
    exact cubeAverage_nonneg_of_nonneg_on henergy_nonneg
  have hW_nonneg : ∀ n : ℕ, 0 ≤ W n := by
    intro n
    dsimp [W]
    refine mul_nonneg ?_ (Real.rpow_nonneg (hM_nonneg n) _)
    have hOld := Homogenization.geometricWeight_nonneg n hsq_nonneg
    simpa [Ch02.geometricWeight_eq_old] using hOld
  have hsumW : Summable W := by
    simpa [W] using hsum
  have htsumW : (∑' n : ℕ, W n) = Lpow := by
    simpa [W] using htsum
  have hpartial :
      ∀ N : ℕ,
        negativeBesovVectorPartialNormFinite Q s q N F ≤
          Real.rpow
            ((Ch02.geometricDiscount s q)⁻¹ * Lpow *
                Real.rpow E (q / 2))
            (1 / q) := by
    intro N
    have hsum_bound :
        Finset.sum (Finset.range (N + 1)) (fun j =>
            Real.rpow (negativeBesovVectorDepthSeminorm Q s F j) q)
          ≤
        (Ch02.geometricDiscount s q)⁻¹ *
          Finset.sum (Finset.range (N + 1)) W *
            Real.rpow E (q / 2) := by
      calc
        Finset.sum (Finset.range (N + 1)) (fun j =>
            Real.rpow (negativeBesovVectorDepthSeminorm Q s F j) q)
            ≤
          Finset.sum (Finset.range (N + 1)) (fun j =>
            (Ch02.geometricDiscount s q)⁻¹ * W j *
              Real.rpow E (q / 2)) := by
            refine Finset.sum_le_sum ?_
            intro j _hj
            have havg :
                negativeBesovVectorDepthAverage Q F j ≤ M j * E := by
              simpa [E] using hdepthAverage j
            have hME_nonneg : 0 ≤ M j * E := mul_nonneg (hM_nonneg j) hE_nonneg
            have hweight_nonneg :
                0 ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) :=
              Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
            have hdepth_le :
                negativeBesovVectorDepthSeminorm Q s F j ≤
                  Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                    Real.sqrt (M j * E) := by
              unfold negativeBesovVectorDepthSeminorm
              exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt havg) hweight_nonneg
            calc
              Real.rpow (negativeBesovVectorDepthSeminorm Q s F j) q
                  ≤
                Real.rpow
                  (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                    Real.sqrt (M j * E)) q := by
                  exact Real.rpow_le_rpow
                    (negativeBesovVectorDepthSeminorm_nonneg Q s F j) hdepth_le hqpos.le
              _ =
                (Ch02.geometricDiscount s q)⁻¹ * W j *
                  Real.rpow E (q / 2) := by
                  have hbase3_nonneg :
                      0 ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) :=
                    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
                  have hsqrt_nonneg : 0 ≤ Real.sqrt (M j * E) := Real.sqrt_nonneg _
                  have hpow_weight :
                      Real.rpow (Real.rpow (3 : ℝ) (-s * (j : ℝ))) q =
                        Real.rpow (3 : ℝ) (-s * (j : ℝ) * q) := by
                    exact (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))
                      (-s * (j : ℝ)) q).symm
                  have hsqrt_pow :
                      Real.rpow (Real.sqrt (M j * E)) q =
                        Real.rpow (M j) (q / 2) * Real.rpow E (q / 2) := by
                    calc
                      Real.rpow (Real.sqrt (M j * E)) q =
                          Real.rpow (Real.rpow (M j * E) (1 / 2 : ℝ)) q := by
                            exact congrArg (fun t => Real.rpow t q)
                              (Real.sqrt_eq_rpow (M j * E))
                      _ = Real.rpow (M j * E) ((1 / 2 : ℝ) * q) := by
                            exact (Real.rpow_mul hME_nonneg (1 / 2 : ℝ) q).symm
                      _ = Real.rpow (M j * E) (q / 2) := by ring_nf
                      _ = Real.rpow (M j) (q / 2) * Real.rpow E (q / 2) := by
                            exact Real.mul_rpow (hM_nonneg j) hE_nonneg
                  calc
                    Real.rpow
                        (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                          Real.sqrt (M j * E)) q =
                      Real.rpow (Real.rpow (3 : ℝ) (-s * (j : ℝ))) q *
                        Real.rpow (Real.sqrt (M j * E)) q := by
                        exact Real.mul_rpow hbase3_nonneg hsqrt_nonneg
                    _ =
                      Real.rpow (3 : ℝ) (-s * (j : ℝ) * q) *
                        (Real.rpow (M j) (q / 2) * Real.rpow E (q / 2)) := by
                        rw [hpow_weight, hsqrt_pow]
                    _ =
                      (Ch02.geometricDiscount s q)⁻¹ * W j *
                        Real.rpow E (q / 2) := by
                        rw [rpow_inv_geometricDiscount_mul_geometricWeight hs hqpos j]
                        dsimp [W]
                        ring
        _ =
          (Ch02.geometricDiscount s q)⁻¹ *
            Finset.sum (Finset.range (N + 1)) W *
              Real.rpow E (q / 2) := by
            calc
              Finset.sum (Finset.range (N + 1)) (fun j =>
                  (Ch02.geometricDiscount s q)⁻¹ * W j *
                    Real.rpow E (q / 2))
                  =
                Finset.sum (Finset.range (N + 1)) (fun j =>
                  ((Ch02.geometricDiscount s q)⁻¹ * Real.rpow E (q / 2)) * W j) := by
                  refine Finset.sum_congr rfl ?_
                  intro j _hj
                  ring
              _ =
                ((Ch02.geometricDiscount s q)⁻¹ * Real.rpow E (q / 2)) *
                  Finset.sum (Finset.range (N + 1)) W := by
                  rw [Finset.mul_sum]
              _ =
                (Ch02.geometricDiscount s q)⁻¹ *
                  Finset.sum (Finset.range (N + 1)) W *
                    Real.rpow E (q / 2) := by
                  ring
    have hfinite_le_tsum :
        Finset.sum (Finset.range (N + 1)) W ≤ ∑' n : ℕ, W n :=
      hsumW.sum_le_tsum (Finset.range (N + 1)) (fun n _ => hW_nonneg n)
    have hsum_le :
        Finset.sum (Finset.range (N + 1)) (fun j =>
            Real.rpow (negativeBesovVectorDepthSeminorm Q s F j) q)
          ≤
        (Ch02.geometricDiscount s q)⁻¹ * Lpow *
          Real.rpow E (q / 2) := by
      calc
        Finset.sum (Finset.range (N + 1)) (fun j =>
            Real.rpow (negativeBesovVectorDepthSeminorm Q s F j) q)
            ≤
          (Ch02.geometricDiscount s q)⁻¹ *
            Finset.sum (Finset.range (N + 1)) W *
              Real.rpow E (q / 2) := hsum_bound
        _ ≤
          (Ch02.geometricDiscount s q)⁻¹ *
            (∑' n : ℕ, W n) *
              Real.rpow E (q / 2) := by
            have hscaled :
                (Ch02.geometricDiscount s q)⁻¹ *
                    Finset.sum (Finset.range (N + 1)) W ≤
                  (Ch02.geometricDiscount s q)⁻¹ * (∑' n : ℕ, W n) :=
              mul_le_mul_of_nonneg_left hfinite_le_tsum (inv_nonneg.mpr hdisc_pos.le)
            exact mul_le_mul_of_nonneg_right hscaled (Real.rpow_nonneg hE_nonneg _)
        _ =
          (Ch02.geometricDiscount s q)⁻¹ * Lpow *
            Real.rpow E (q / 2) := by
            rw [htsumW]
    unfold negativeBesovVectorPartialNormFinite
    have hleft_nonneg :
        0 ≤ Finset.sum (Finset.range (N + 1)) (fun j =>
          Real.rpow (negativeBesovVectorDepthSeminorm Q s F j) q) :=
      Finset.sum_nonneg fun j _ =>
        Real.rpow_nonneg (negativeBesovVectorDepthSeminorm_nonneg Q s F j) _
    exact Real.rpow_le_rpow hleft_nonneg hsum_le (one_div_nonneg.mpr hqpos.le)
  exact scaleNormalizedNegativeBesovVectorNorm_finite_le_of_partialBound Q s q F hpartial

theorem finite_gradient_norm_le_of_cubeAverageEnergyControl {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffFamily d)
    (s q : ℝ) (hs : 0 < s) (hq : 1 ≤ q)
    (F : Vec d → Vec d) (energy : Vec d → ℝ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (hdepthAverage :
      ∀ n : ℕ,
        negativeBesovVectorDepthAverage Q F n ≤
          Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a *
            cubeAverage Q energy)
    (hsum :
      Summable fun n : ℕ =>
        Ch02.geometricWeight s q n *
          Real.rpow
            (Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
            (q / 2))
    (htsum :
      (∑' n : ℕ,
        Ch02.geometricWeight s q n *
          Real.rpow
            (Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
            (q / 2)) =
        Real.rpow (Ch02.lambdaSq Q s (.finite q) a) (-q / 2)) :
    scaleNormalizedNegativeBesovVectorNorm Q s (.finite q) F ≤
      poincareDiscountFactor s (.finite q) *
        poincareLowerEllipticityFactor Q a s (.finite q) *
          Real.sqrt (cubeAverage Q energy) := by
  have hM_nonneg :
      ∀ n : ℕ,
        0 ≤ Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a := by
    intro n
    exact Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hbase :
      scaleNormalizedNegativeBesovVectorNorm Q s (.finite q) F ≤
        Real.rpow
          ((Ch02.geometricDiscount s q)⁻¹ *
            Real.rpow (Ch02.lambdaSq Q s (.finite q) a) (-q / 2) *
              Real.rpow (cubeAverage Q energy) (q / 2))
          (1 / q) := by
    exact finite_norm_le_of_depthAverage_tsum
      (Q := Q) (s := s) (q := q) (hs := hs) (hq := hq)
      (F := F) (energy := energy)
      (M := fun n =>
        Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
      (Lpow := Real.rpow (Ch02.lambdaSq Q s (.finite q) a) (-q / 2))
      (henergy_nonneg := henergy_nonneg)
      (hM_nonneg := hM_nonneg)
      (hdepthAverage := hdepthAverage)
      (hsum := hsum)
      (htsum := htsum)
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hdisc_pos : 0 < Ch02.geometricDiscount s q := by
    have h := Homogenization.geometricDiscount_pos (mul_pos hs hqpos)
    simpa [Ch02.geometricDiscount, Homogenization.geometricDiscount] using h
  have hE_nonneg : 0 ≤ cubeAverage Q energy := by
    exact cubeAverage_nonneg_of_nonneg_on henergy_nonneg
  have hlambda_nonneg : 0 ≤ Ch02.lambdaSq Q s (.finite q) a :=
    Ch02.lambdaSq_finite_nonneg Q a hs hq
  calc
    scaleNormalizedNegativeBesovVectorNorm Q s (.finite q) F
        ≤
          Real.rpow
            ((Ch02.geometricDiscount s q)⁻¹ *
              Real.rpow (Ch02.lambdaSq Q s (.finite q) a) (-q / 2) *
                Real.rpow (cubeAverage Q energy) (q / 2))
            (1 / q) := hbase
    _ =
      poincareDiscountFactor s (.finite q) *
        poincareLowerEllipticityFactor Q a s (.finite q) *
          Real.sqrt (cubeAverage Q energy) := by
      rw [rpow_finite_gradient_rhs hdisc_pos hlambda_nonneg hE_nonneg hqpos]
      rfl

theorem finite_flux_norm_le_of_cubeAverageEnergyControl {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffFamily d)
    (s q : ℝ) (hs : 0 < s) (hq : 1 ≤ q)
    (F : Vec d → Vec d) (energy : Vec d → ℝ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (hdepthAverage :
      ∀ n : ℕ,
        negativeBesovVectorDepthAverage Q F n ≤
          Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a *
            cubeAverage Q energy)
    (hsum :
      Summable fun n : ℕ =>
        Ch02.geometricWeight s q n *
          Real.rpow
            (Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
            (q / 2))
    (htsum :
      (∑' n : ℕ,
        Ch02.geometricWeight s q n *
          Real.rpow
            (Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
            (q / 2)) =
        Real.rpow (Ch02.LambdaSq Q s (.finite q) a) (q / 2)) :
    scaleNormalizedNegativeBesovVectorNorm Q s (.finite q) F ≤
      poincareDiscountFactor s (.finite q) *
        poincareUpperEllipticityFactor Q a s (.finite q) *
          Real.sqrt (cubeAverage Q energy) := by
  have hM_nonneg :
      ∀ n : ℕ,
        0 ≤ Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a := by
    intro n
    exact Ch02.maxDescendantBMatrixNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hbase :
      scaleNormalizedNegativeBesovVectorNorm Q s (.finite q) F ≤
        Real.rpow
          ((Ch02.geometricDiscount s q)⁻¹ *
            Real.rpow (Ch02.LambdaSq Q s (.finite q) a) (q / 2) *
              Real.rpow (cubeAverage Q energy) (q / 2))
          (1 / q) := by
    exact finite_norm_le_of_depthAverage_tsum
      (Q := Q) (s := s) (q := q) (hs := hs) (hq := hq)
      (F := F) (energy := energy)
      (M := fun n =>
        Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
      (Lpow := Real.rpow (Ch02.LambdaSq Q s (.finite q) a) (q / 2))
      (henergy_nonneg := henergy_nonneg)
      (hM_nonneg := hM_nonneg)
      (hdepthAverage := hdepthAverage)
      (hsum := hsum)
      (htsum := htsum)
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hdisc_pos : 0 < Ch02.geometricDiscount s q := by
    have h := Homogenization.geometricDiscount_pos (mul_pos hs hqpos)
    simpa [Ch02.geometricDiscount, Homogenization.geometricDiscount] using h
  have hE_nonneg : 0 ≤ cubeAverage Q energy := by
    exact cubeAverage_nonneg_of_nonneg_on henergy_nonneg
  have hLambda_nonneg : 0 ≤ Ch02.LambdaSq Q s (.finite q) a :=
    Ch02.LambdaSq_finite_nonneg Q a hs hq
  calc
    scaleNormalizedNegativeBesovVectorNorm Q s (.finite q) F
        ≤
          Real.rpow
            ((Ch02.geometricDiscount s q)⁻¹ *
              Real.rpow (Ch02.LambdaSq Q s (.finite q) a) (q / 2) *
                Real.rpow (cubeAverage Q energy) (q / 2))
            (1 / q) := hbase
    _ =
      poincareDiscountFactor s (.finite q) *
        poincareUpperEllipticityFactor Q a s (.finite q) *
          Real.sqrt (cubeAverage Q energy) := by
      rw [rpow_finite_flux_rhs hdisc_pos hLambda_nonneg hE_nonneg hqpos]
      rfl


end

end Ch03
end Book
end Homogenization
