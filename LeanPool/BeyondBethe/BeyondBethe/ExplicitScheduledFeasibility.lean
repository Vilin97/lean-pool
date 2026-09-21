/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.ScheduledFeasibility
import Mathlib.Tactic

/-! # Explicit Scheduled Feasibility -/

open scoped BigOperators

namespace BeyondBethe

/-!
# An explicit schedule for a zero-centered rational ball

Every Bethe feasibility call starts from a zero-centered diagonal ball.  For
that special initial state there is no reason to compute a matrix common
denominator.  The canonical bit length of the radius gives both a dyadic
lower bound on the initial determinant and a dyadic upper bound on the exact
initial state magnitude.  This file packages those two exponents into the
fixed-precision feasibility runner used by the finite-word implementation.
-/

def explicitBallInitialDetExponent (d : ℕ) (R : ℚ) : ℕ :=
  encodedBitLength ℚ R * d

def explicitBallInitialMagnitudeBound (d : ℕ) (R : ℚ) : ℚ :=
  2 + d * R

def explicitBallInitialMagnitudeExponent (d : ℕ) (R : ℚ) : ℕ :=
  encodedBitLength ℚ (explicitBallInitialMagnitudeBound d R)

def explicitBallFeasibilityPrecision (d budget : ℕ) (R : ℚ) : ℕ :=
  roundedEllipsoidPrecisionSchedule d
    (explicitBallInitialDetExponent d R)
    (explicitBallInitialMagnitudeExponent d R) budget

def runExplicitBallRationalFeasibility {d : ℕ}
    (oracle : RationalCentralOracle d) (budget : ℕ) (R : ℚ) :
    RationalFeasibilityResult d :=
  runFixedPrecisionRationalFeasibility
    (explicitBallFeasibilityPrecision d budget R) oracle budget
    (rationalBallEllipsoid d 0 R)

theorem explicitBallInitialDetExponent_lower {d : ℕ} {R : ℚ}
    (hR : 0 < R) :
    dyadicMesh (explicitBallInitialDetExponent d R) ≤ R ^ d := by
  let L := encodedBitLength ℚ R
  have hlower : dyadicMesh L < R := by
    rw [dyadicMesh_eq_half_pow]
    simpa only [L] using dyadic_encodedBitLength_lt_positive_rational hR
  have hlower' : dyadicMesh L ≤ R := hlower.le
  have hpow : dyadicMesh L ^ d ≤ R ^ d :=
    pow_le_pow_left₀ (dyadicMesh_nonneg L) hlower' d
  rw [explicitBallInitialDetExponent, dyadicMesh_eq_half_pow]
  rw [show encodedBitLength ℚ R * d = L * d by rfl, pow_mul]
  simpa only [dyadicMesh_eq_half_pow] using hpow

theorem rationalStateAbsBound_zero_ball {d : ℕ} {R : ℚ}
    (hR : 0 ≤ R) :
    rationalStateAbsBound (rationalBallEllipsoid d 0 R) =
      explicitBallInitialMagnitudeBound d R := by
  classical
  rw [rationalStateAbsBound, rationalCenterAbsBound,
    rationalMatrixAbsBound, explicitBallInitialMagnitudeBound]
  simp only [rationalBallEllipsoid, Pi.zero_apply, abs_zero,
    Finset.sum_const_zero, zero_add]
  have hinner (i : Fin d) :
      (∑ j : Fin d, abs (if i = j then R else 0)) = R := by
    calc
      (∑ j : Fin d, abs (if i = j then R else 0)) =
          ∑ j : Fin d, if i = j then R else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i = j <;> simp [hij, abs_of_nonneg hR]
      _ = R := by
        simpa using Fintype.sum_ite_eq i (fun _ : Fin d ↦ R)
  have hsum :
      (∑ i : Fin d, ∑ j : Fin d, abs (if i = j then R else 0)) =
        ∑ _i : Fin d, R := by
      apply Finset.sum_congr rfl
      intro i _
      exact hinner i
  rw [hsum]
  simp
  ring

theorem explicitBallInitialMagnitudeExponent_upper {d : ℕ} {R : ℚ}
    (hR : 0 < R) :
    rationalStateAbsBound (rationalBallEllipsoid d 0 R) ≤
      (2 : ℚ) ^ explicitBallInitialMagnitudeExponent d R := by
  rw [rationalStateAbsBound_zero_ball hR.le]
  have hbound : 0 < explicitBallInitialMagnitudeBound d R := by
    rw [explicitBallInitialMagnitudeBound]
    positivity
  exact (positive_rational_lt_two_pow_encodedBitLength hbound).le

theorem explicitBallInitialInvariant {d : ℕ} {R : ℚ}
    (hR : 0 < R) :
    ScheduledEllipsoidInvariant d
      (explicitBallInitialDetExponent d R)
      (explicitBallInitialMagnitudeExponent d R) 0
      (rationalBallEllipsoid d 0 R) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [det_rationalBallEllipsoid]
    exact pow_ne_zero d hR.ne'
  · rw [det_rationalBallEllipsoid, abs_of_pos (pow_pos hR d)]
    simpa using explicitBallInitialDetExponent_lower hR
  · simpa using explicitBallInitialMagnitudeExponent_upper hR

theorem runExplicitBallRationalFeasibility_acceptsOnly {d : ℕ}
    {Good : (Fin d → ℚ) → Prop} {oracle : RationalCentralOracle d}
    (haccept : RationalCentralOracleAcceptsOnly Good oracle)
    {budget : ℕ} {R : ℚ} {x : Fin d → ℚ}
    (hrun : runExplicitBallRationalFeasibility oracle budget R =
      .accepted x) : Good x := by
  exact runFixedPrecisionRationalFeasibility_acceptsOnly haccept
    (by simpa only [runExplicitBallRationalFeasibility] using hrun)

theorem runExplicitBallRationalFeasibility_not_exhausted_of_inner_cross
    {d M : ℕ} (hd : 0 < d)
    {Target : (Fin d → ℝ) → Prop} {oracle : RationalCentralOracle d}
    (hvalid : RationalCentralOracleValid Target oracle)
    {R : ℚ} (hR : 0 < R)
    {z : Fin d → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hdyadic : d.factorial * (R : ℝ) ^ d *
      (1 / 2 : ℝ) ^ M < r ^ d)
    (hTargetPlus : ∀ k, Target
      (fun i ↦ z i + if i = k then r else 0))
    (hTargetMinus : ∀ k, Target
      (fun i ↦ z i - if i = k then r else 0))
    (hEplus : ∀ k, RationalEllipsoidContains
      (rationalBallEllipsoid d 0 R)
      (fun i ↦ z i + if i = k then r else 0))
    (hEminus : ∀ k, RationalEllipsoidContains
      (rationalBallEllipsoid d 0 R)
      (fun i ↦ z i - if i = k then r else 0))
    (E' : RationalEllipsoidState d) :
    runExplicitBallRationalFeasibility oracle (32 * d ^ 3 * M) R ≠
      .exhausted E' := by
  intro hrun
  let L := explicitBallInitialDetExponent d R
  let K := explicitBallInitialMagnitudeExponent d R
  let T := 32 * d ^ 3 * M
  let E := rationalBallEllipsoid d 0 R
  have hInv : ScheduledEllipsoidInvariant d L K 0 E := by
    simpa only [L, K, E] using explicitBallInitialInvariant hR
  have hrun' : runFixedPrecisionRationalFeasibility
      (roundedEllipsoidPrecisionSchedule d L K T) oracle T E =
        .exhausted E' := by
    simpa only [runExplicitBallRationalFeasibility,
      explicitBallFeasibilityPrecision, L, K, T, E] using hrun
  have hplus : ∀ k, RationalEllipsoidContains E'
      (fun i ↦ z i + if i = k then r else 0) := by
    intro k
    exact runFixedPrecisionRationalFeasibility_preserves_target_of_exhausted
      hd hvalid hInv (by omega) hrun' (hTargetPlus k) (hEplus k)
  have hminus : ∀ k, RationalEllipsoidContains E'
      (fun i ↦ z i - if i = k then r else 0) := by
    intro k
    exact runFixedPrecisionRationalFeasibility_preserves_target_of_exhausted
      hd hvalid hInv (by omega) hrun' (hTargetMinus k) (hEminus k)
  have hlower := rationalEllipsoid_storedDet_lower_of_ball_endpoints
    E' hr (fun k ↦ hplus k) (fun k ↦ hminus k)
  have hupper := runFixedPrecisionRationalFeasibility_det_upper_of_exhausted
    hd hvalid hInv (by omega) hrun'
  have hfactor := roundedContractionFactor_pow_budget_le_half_pow
    (d := d) (M := M) hd
  have hdetUpper : abs ((Matrix.det E'.basis : ℚ) : ℝ) ≤
      (1 / 2 : ℝ) ^ M * (R : ℝ) ^ d := by
    rw [show abs ((Matrix.det E.basis : ℚ) : ℝ) = (R : ℝ) ^ d by
      dsimp only [E]
      rw [det_rationalBallEllipsoid, Rat.cast_pow,
        abs_of_pos (pow_pos (Rat.cast_pos.mpr hR) d)]] at hupper
    exact hupper.trans
      (mul_le_mul_of_nonneg_right hfactor (by positivity))
  have hsandwich : r ^ d ≤
      d.factorial * (R : ℝ) ^ d * (1 / 2 : ℝ) ^ M := by
    calc
      r ^ d ≤ d.factorial *
          abs ((Matrix.det E'.basis : ℚ) : ℝ) := hlower
      _ ≤ d.factorial * ((1 / 2 : ℝ) ^ M * (R : ℝ) ^ d) :=
        mul_le_mul_of_nonneg_left hdetUpper (Nat.cast_nonneg _)
      _ = d.factorial * (R : ℝ) ^ d * (1 / 2 : ℝ) ^ M := by ring
  exact (not_lt_of_ge hsandwich) hdyadic

theorem runExplicitBallRationalFeasibility_ball_accepts
    {d : ℕ} (hd : 0 < d)
    {Target : (Fin d → ℝ) → Prop} {Good : (Fin d → ℚ) → Prop}
    {oracle : RationalCentralOracle d}
    (hvalid : RationalCentralOracleValid Target oracle)
    (haccept : RationalCentralOracleAcceptsOnly Good oracle)
    {R r : ℚ} (hR : 0 < R) (hr : 0 < r)
    {z : Fin d → ℝ}
    (hTargetPlus : ∀ k, Target
      (fun i ↦ z i + if i = k then (r : ℝ) else 0))
    (hTargetMinus : ∀ k, Target
      (fun i ↦ z i - if i = k then (r : ℝ) else 0))
    (houterPlus : ∀ k, finiteNormSq
      (fun i ↦ z i + if i = k then (r : ℝ) else 0) ≤ (R : ℝ) ^ 2)
    (houterMinus : ∀ k, finiteNormSq
      (fun i ↦ z i - if i = k then (r : ℝ) else 0) ≤ (R : ℝ) ^ 2) :
    let M := rationalBallDyadicExponent d R r
    let budget := 32 * d ^ 3 * M
    ∃ x : Fin d → ℚ,
      runExplicitBallRationalFeasibility oracle budget R = .accepted x ∧
        Good x := by
  dsimp only
  let M := rationalBallDyadicExponent d R r
  let budget := 32 * d ^ 3 * M
  let result := runExplicitBallRationalFeasibility oracle budget R
  cases hresult : result with
  | accepted x =>
      refine ⟨x, ?_, ?_⟩
      · simpa only [result, budget, M] using hresult
      · exact runExplicitBallRationalFeasibility_acceptsOnly haccept
          (by simpa only [result, budget, M] using hresult)
  | exhausted E' =>
      exfalso
      apply runExplicitBallRationalFeasibility_not_exhausted_of_inner_cross
        hd hvalid hR (hr := Rat.cast_nonneg.mpr hr.le)
          (by
            have hbudget := rationalBallEllipsoid_dyadic_budget
              hd (0 : Fin d → ℚ) hR hr
            rw [det_rationalBallEllipsoid, Rat.cast_pow,
              abs_of_pos (pow_pos (Rat.cast_pos.mpr hR) d)] at hbudget
            simpa only [M] using hbudget)
          hTargetPlus hTargetMinus
      · intro k
        apply rationalBallEllipsoid_contains 0 hR
        simpa using houterPlus k
      · intro k
        apply rationalBallEllipsoid_contains 0 hR
        simpa using houterMinus k
      · simpa only [result, budget, M] using hresult

end BeyondBethe
