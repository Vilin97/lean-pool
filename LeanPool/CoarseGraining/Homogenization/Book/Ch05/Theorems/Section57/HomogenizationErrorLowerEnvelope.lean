/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.NormalizedResponseEllipticity
public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarsePoincare.Finite

/-! # Homogenization Error Lower Envelope -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open scoped MatrixOrder BigOperators

/-!
# Lower-scale response envelope

This file supplies the deterministic lower-scale input for the closed
`\mathcal E` estimate.  The results here keep the lower-scale contribution in
the same algebraic envelope used by the main finite-`q` summation.
-/

noncomputable section

/-- A negative-scale response row is controlled by the scale-zero Ch2
ellipticity suprema, with the same weight as in the homogenization-error
series. -/
theorem weighted_negative_scaleResponse_le_scaleZero_ellipticity_roots
    {d : ℕ} [NeZero d]
    (m j : ℕ) {s σ : ℝ} (hs : 0 < s) (hσ : 0 < σ)
    (a : Ch02.TriadicCoeffFamily d) :
    let Q : TriadicCube d := originCube d ((m : ℕ) : ℤ);
    let D : Finset (TriadicCube d) := descendantsAtScale Q 0;
    let hD : D.Nonempty := descendantsAtScale_nonempty Q (by simp [Q, originCube]);
    Ch02.geometricWeight s 1 (j + m) *
        Ch02.scaleResponseAtScale Q (-(j : ℤ))
          Ch02.MultiscaleExponent.infinity a (scalarMatrix (d := d) σ) ≤
      Real.sqrt ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
        (Real.sqrt σ⁻¹ *
            (Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
              Real.rpow (D.sup' hD (fun U => Ch02.LambdaSq U s (.finite 1) a))
                (1 / 2 : ℝ)) +
          Real.sqrt σ *
            (Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
              Real.rpow
                (D.sup' hD (fun U => (Ch02.lambdaSq U s (.finite 1) a)⁻¹))
                (1 / 2 : ℝ))) := by
  classical
  intro Q D hD
  let C : ℝ := (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)
  let upperRow : ℝ :=
    Ch02.geometricWeight s 1 (j + m) *
      Real.rpow
        (Ch02.maxDescendantBMatrixNormAtScale Q (-(j : ℤ)) a)
        (1 / 2 : ℝ)
  let lowerRow : ℝ :=
    Ch02.geometricWeight s 1 (j + m) *
      Real.rpow
        (Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (-(j : ℤ)) a)
        (1 / 2 : ℝ)
  let upperRoot : ℝ :=
    Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
      Real.rpow (D.sup' hD (fun U => Ch02.LambdaSq U s (.finite 1) a))
        (1 / 2 : ℝ)
  let lowerRoot : ℝ :=
    Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
      Real.rpow (D.sup' hD (fun U => (Ch02.lambdaSq U s (.finite 1) a)⁻¹))
        (1 / 2 : ℝ)
  have hrow :=
    weighted_scaleResponseAtScale_originCube_neg_nat_scalarMatrix_le_ellipticityRows
      (d := d) m j (s := s) (σ := σ) hs.le hσ a
  have hupper : upperRow ≤ upperRoot := by
    simpa [Q, D, hD, upperRow, upperRoot] using
      Ch02.upperSmallSqrtTailTerm_le_scale_factor_mul_scale_zero_LambdaSq_sup'_rpow_half
        (d := d) m j hs a
  have hlower : lowerRow ≤ lowerRoot := by
    simpa [Q, D, hD, lowerRow, lowerRoot] using
      Ch02.lowerSmallSqrtTailTerm_le_scale_factor_mul_scale_zero_lambdaSq_inv_sup'_rpow_half
        (d := d) m j hs a
  have hsqrt_inv_nonneg : 0 ≤ Real.sqrt σ⁻¹ := Real.sqrt_nonneg σ⁻¹
  have hsqrt_nonneg : 0 ≤ Real.sqrt σ := Real.sqrt_nonneg σ
  have hinside :
      Real.sqrt σ⁻¹ * upperRow + Real.sqrt σ * lowerRow ≤
        Real.sqrt σ⁻¹ * upperRoot + Real.sqrt σ * lowerRoot := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left hupper hsqrt_inv_nonneg)
      (mul_le_mul_of_nonneg_left hlower hsqrt_nonneg)
  have hC_nonneg : 0 ≤ Real.sqrt C := by
    exact Real.sqrt_nonneg C
  exact hrow.trans (by
    exact mul_le_mul_of_nonneg_left hinside hC_nonneg)

/-- If the scale-zero ellipticity suprema are already in the collapsed
minimal-scale envelope, then every negative response row is in the same
weighted envelope. -/
theorem weighted_negative_scaleResponse_le_of_scaleZero_collapsed
    {d : ℕ} [NeZero d]
    (m j : ℕ) {s σ R : ℝ} (hs : 0 < s) (hσ : 0 < σ) (hR : 0 ≤ R)
    (a : Ch02.TriadicCoeffFamily d)
    (hupper :
      let Q : TriadicCube d := originCube d ((m : ℕ) : ℤ);
      let D : Finset (TriadicCube d) := descendantsAtScale Q 0;
      let hD : D.Nonempty := descendantsAtScale_nonempty Q (by simp [Q, originCube]);
      σ⁻¹ * D.sup' hD (fun U => Ch02.LambdaSq U s (.finite 1) a) ≤
        (Real.rpow (3 : ℝ) (s * (m : ℝ)) * R) ^ (2 : ℕ))
    (hlower :
      let Q : TriadicCube d := originCube d ((m : ℕ) : ℤ);
      let D : Finset (TriadicCube d) := descendantsAtScale Q 0;
      let hD : D.Nonempty := descendantsAtScale_nonempty Q (by simp [Q, originCube]);
      σ * D.sup' hD (fun U => (Ch02.lambdaSq U s (.finite 1) a)⁻¹) ≤
        (Real.rpow (3 : ℝ) (s * (m : ℝ)) * R) ^ (2 : ℕ)) :
    Ch02.geometricWeight s 1 (j + m) *
        Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ)) (-(j : ℤ))
          Ch02.MultiscaleExponent.infinity a (scalarMatrix (d := d) σ) ≤
      (2 * Real.sqrt ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ))) * R := by
  classical
  let Q : TriadicCube d := originCube d ((m : ℕ) : ℤ)
  let D : Finset (TriadicCube d) := descendantsAtScale Q 0
  let hD : D.Nonempty := descendantsAtScale_nonempty Q (by simp [Q, originCube])
  let C : ℝ := (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)
  let M : ℝ := Real.rpow (3 : ℝ) (s * (m : ℝ)) * R
  let upperSup : ℝ := D.sup' hD (fun U => Ch02.LambdaSq U s (.finite 1) a)
  let lowerSup : ℝ := D.sup' hD (fun U => (Ch02.lambdaSq U s (.finite 1) a)⁻¹)
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hupperSup_nonneg : 0 ≤ upperSup := by
    rcases hD with ⟨U, hU⟩
    exact (Ch02.LambdaSq_finite_nonneg U a hs
      (by norm_num : (1 : ℝ) ≤ 1)).trans
        (Finset.le_sup' (s := D)
          (f := fun U => Ch02.LambdaSq U s (.finite 1) a) hU)
  have hlowerSup_nonneg : 0 ≤ lowerSup := by
    rcases hD with ⟨U, hU⟩
    exact (inv_nonneg.mpr
      (Ch02.lambdaSq_finite_nonneg U a hs
        (by norm_num : (1 : ℝ) ≤ 1))).trans
        (Finset.le_sup' (s := D)
          (f := fun U => (Ch02.lambdaSq U s (.finite 1) a)⁻¹) hU)
  have hupperRoot :
      Real.sqrt σ⁻¹ * Real.rpow upperSup (1 / 2 : ℝ) ≤ M := by
    have hmul_nonneg : 0 ≤ σ⁻¹ * upperSup :=
      mul_nonneg (inv_pos.mpr hσ).le hupperSup_nonneg
    have hroot_le :
        Real.sqrt (σ⁻¹ * upperSup) ≤ Real.sqrt (M ^ (2 : ℕ)) :=
      Real.sqrt_le_sqrt (by simpa [Q, D, hD, M, upperSup] using hupper)
    have hroot_eq :
        Real.sqrt (σ⁻¹ * upperSup) =
          Real.sqrt σ⁻¹ * Real.rpow upperSup (1 / 2 : ℝ) := by
      rw [Real.sqrt_mul (inv_pos.mpr hσ).le]
      simp [Real.sqrt_eq_rpow]
    rw [hroot_eq] at hroot_le
    simpa [Real.sqrt_sq hM_nonneg] using hroot_le
  have hlowerRoot :
      Real.sqrt σ * Real.rpow lowerSup (1 / 2 : ℝ) ≤ M := by
    have hmul_nonneg : 0 ≤ σ * lowerSup :=
      mul_nonneg hσ.le hlowerSup_nonneg
    have hroot_le :
        Real.sqrt (σ * lowerSup) ≤ Real.sqrt (M ^ (2 : ℕ)) :=
      Real.sqrt_le_sqrt (by simpa [Q, D, hD, M, lowerSup] using hlower)
    have hroot_eq :
        Real.sqrt (σ * lowerSup) =
          Real.sqrt σ * Real.rpow lowerSup (1 / 2 : ℝ) := by
      rw [Real.sqrt_mul hσ.le]
      simp [Real.sqrt_eq_rpow]
    rw [hroot_eq] at hroot_le
    simpa [Real.sqrt_sq hM_nonneg] using hroot_le
  have hweighted :=
    weighted_negative_scaleResponse_le_scaleZero_ellipticity_roots
      (d := d) m j (s := s) (σ := σ) hs hσ a
  have hinside :
      Real.sqrt σ⁻¹ *
          (Real.rpow (3 : ℝ) (-s * (m : ℝ)) * Real.rpow upperSup (1 / 2 : ℝ)) +
        Real.sqrt σ *
          (Real.rpow (3 : ℝ) (-s * (m : ℝ)) * Real.rpow lowerSup (1 / 2 : ℝ))
        ≤ 2 * R := by
    have hfactor_pos : 0 < Real.rpow (3 : ℝ) (-s * (m : ℝ)) := by
      exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _
    have hfactor_mul_M :
        Real.rpow (3 : ℝ) (-s * (m : ℝ)) * M = R := by
      dsimp [M]
      have hp : 0 < Real.rpow (3 : ℝ) (s * (m : ℝ)) :=
        Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _
      rw [show -s * (m : ℝ) = -(s * (m : ℝ)) by ring]
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
      field_simp [hp.ne']
    calc
      Real.sqrt σ⁻¹ *
          (Real.rpow (3 : ℝ) (-s * (m : ℝ)) * Real.rpow upperSup (1 / 2 : ℝ)) +
        Real.sqrt σ *
          (Real.rpow (3 : ℝ) (-s * (m : ℝ)) * Real.rpow lowerSup (1 / 2 : ℝ))
          =
        Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
          (Real.sqrt σ⁻¹ * Real.rpow upperSup (1 / 2 : ℝ) +
            Real.sqrt σ * Real.rpow lowerSup (1 / 2 : ℝ)) := by
            ring
      _ ≤ Real.rpow (3 : ℝ) (-s * (m : ℝ)) * (M + M) := by
            exact mul_le_mul_of_nonneg_left
              (add_le_add hupperRoot hlowerRoot) hfactor_pos.le
      _ = 2 * R := by
            rw [show M + M = 2 * M by ring]
            calc
              Real.rpow (3 : ℝ) (-s * (m : ℝ)) * (2 * M)
                  = 2 * (Real.rpow (3 : ℝ) (-s * (m : ℝ)) * M) := by
                    ring
              _ = 2 * R := by rw [hfactor_mul_M]
  have hC_nonneg : 0 ≤ Real.sqrt C := Real.sqrt_nonneg C
  calc
    Ch02.geometricWeight s 1 (j + m) *
        Ch02.scaleResponseAtScale Q (-(j : ℤ))
          Ch02.MultiscaleExponent.infinity a (scalarMatrix (d := d) σ)
        ≤ Real.sqrt C *
          (Real.sqrt σ⁻¹ *
              (Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
                Real.rpow upperSup (1 / 2 : ℝ)) +
            Real.sqrt σ *
              (Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
                Real.rpow lowerSup (1 / 2 : ℝ))) := by
          simpa [Q, D, hD, C, upperSup, lowerSup] using hweighted
    _ ≤ Real.sqrt C * (2 * R) :=
          mul_le_mul_of_nonneg_left hinside hC_nonneg
    _ = (2 * Real.sqrt C) * R := by ring

/-- Weighted negative-scale response control gives the unweighted algebraic
scale envelope, paying only the fixed geometric-discount constant. -/
theorem negative_scaleResponse_le_of_weighted_envelope
    {d : ℕ} [NeZero d]
    (m j : ℕ) {s σ A R : ℝ} (hs : 0 < s) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (a : Ch02.TriadicCoeffFamily d)
    (hweighted :
      Ch02.geometricWeight s 1 (j + m) *
          Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ)) (-(j : ℤ))
            Ch02.MultiscaleExponent.infinity a (scalarMatrix (d := d) σ) ≤
        A * R) :
    Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ)) (-(j : ℤ))
        Ch02.MultiscaleExponent.infinity a (scalarMatrix (d := d) σ) ≤
      (Ch02.geometricDiscount s 1)⁻¹ * A *
        Real.rpow (3 : ℝ) (s * ((j + m : ℕ) : ℝ)) * R := by
  let resp : ℝ :=
    Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ)) (-(j : ℤ))
      Ch02.MultiscaleExponent.infinity a (scalarMatrix (d := d) σ)
  let w : ℝ := Ch02.geometricWeight s 1 (j + m)
  let Env : ℝ :=
    (Ch02.geometricDiscount s 1)⁻¹ * A *
      Real.rpow (3 : ℝ) (s * ((j + m : ℕ) : ℝ)) * R
  have hw_pos : 0 < w := by
    dsimp [w]
    simpa [Ch02.geometricWeight_eq_old] using
      Homogenization.geometricWeight_pos (s := s) (q := 1) (j + m)
        (by simpa using hs)
  have hdisc_pos : 0 < Ch02.geometricDiscount s 1 := by
    simpa [Ch02.geometricDiscount_eq_old] using
      Homogenization.geometricDiscount_pos (s := s) (q := 1)
        (by simpa using hs)
  have hEnv_nonneg : 0 ≤ Env := by
    dsimp [Env]
    positivity
  have hwEnv : w * Env = A * R := by
    dsimp [w, Env]
    unfold Ch02.geometricWeight
    have hpow_mul :
        Real.rpow (3 : ℝ) (-s * 1 * ((j + m : ℕ) : ℝ)) *
            Real.rpow (3 : ℝ) (s * ((j + m : ℕ) : ℝ)) = 1 := by
      have hp : 0 < Real.rpow (3 : ℝ) (s * ((j + m : ℕ) : ℝ)) :=
        Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _
      calc
        Real.rpow (3 : ℝ) (-s * 1 * ((j + m : ℕ) : ℝ)) *
            Real.rpow (3 : ℝ) (s * ((j + m : ℕ) : ℝ))
            =
          Real.rpow (3 : ℝ) (-(s * ((j + m : ℕ) : ℝ))) *
            Real.rpow (3 : ℝ) (s * ((j + m : ℕ) : ℝ)) := by
            congr 1
            ring_nf
        _ = (Real.rpow (3 : ℝ) (s * ((j + m : ℕ) : ℝ)))⁻¹ *
            Real.rpow (3 : ℝ) (s * ((j + m : ℕ) : ℝ)) := by
            have hneg :
                Real.rpow (3 : ℝ) (-(s * ((j + m : ℕ) : ℝ))) =
                  (Real.rpow (3 : ℝ) (s * ((j + m : ℕ) : ℝ)))⁻¹ :=
              Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)
                (s * ((j + m : ℕ) : ℝ))
            simpa using congrArg
              (fun z => z * Real.rpow (3 : ℝ) (s * ((j + m : ℕ) : ℝ))) hneg
        _ = 1 := inv_mul_cancel₀ hp.ne'
    calc
      (Ch02.geometricDiscount s 1 *
            Real.rpow (3 : ℝ) (-s * 1 * ((j + m : ℕ) : ℝ))) *
          ((Ch02.geometricDiscount s 1)⁻¹ * A *
            Real.rpow (3 : ℝ) (s * ((j + m : ℕ) : ℝ)) * R)
          =
        (Ch02.geometricDiscount s 1 * (Ch02.geometricDiscount s 1)⁻¹) *
          (Real.rpow (3 : ℝ) (-s * 1 * ((j + m : ℕ) : ℝ)) *
            Real.rpow (3 : ℝ) (s * ((j + m : ℕ) : ℝ))) * A * R := by
          ring
      _ = A * R := by
          rw [mul_inv_cancel₀ hdisc_pos.ne', hpow_mul]
          ring
  have hmul : w * resp ≤ w * Env := by
    calc
      w * resp ≤ A * R := by
        simpa [resp, w] using hweighted
      _ = w * Env := hwEnv.symm
  exact le_of_mul_le_mul_left hmul hw_pos

end

end Section57
end Ch05
end Book
end Homogenization
