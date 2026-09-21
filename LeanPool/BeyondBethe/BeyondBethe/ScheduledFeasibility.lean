/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.ScheduledRoundedEllipsoidIteration
import LeanPool.BeyondBethe.BeyondBethe.RationalFeasibility
import LeanPool.BeyondBethe.BeyondBethe.RoundedFeasibility
import Mathlib.Tactic

/-! # Scheduled Feasibility -/

open scoped BigOperators

namespace BeyondBethe

/-!
# Fixed-precision rational feasibility

The public runner computes two determinant-free exponents from its initial
state and one precision from the total iteration budget.  That precision is
then held fixed throughout the recursive loop.
-/

/-- Determinant-free initial exponent. -/
def scheduledInitialDetExponent {d : ℕ}
    (E : RationalEllipsoidState d) : ℕ :=
  positiveDyadicPrecision (rationalMatrixDeterminantLower E.basis)

/-- Initial exponent dominating the total rational state magnitude. -/
def scheduledInitialMagnitudeExponent {d : ℕ}
    (E : RationalEllipsoidState d) : ℕ :=
  encodedBitLength ℚ (rationalStateAbsBound E)

theorem scheduledInitialDetExponent_lower {d : ℕ}
    (E : RationalEllipsoidState d) (hdet : Matrix.det E.basis ≠ 0) :
    dyadicMesh (scheduledInitialDetExponent E) ≤
      abs (Matrix.det E.basis) := by
  exact (dyadicMesh_positiveDyadicPrecision_lt
    (rationalMatrixDeterminantLower_pos E.basis)).le.trans
      (rationalMatrixDeterminantLower_le_abs_det E.basis hdet)

theorem scheduledInitialMagnitudeExponent_upper {d : ℕ}
    (E : RationalEllipsoidState d) :
    rationalStateAbsBound E ≤
      (2 : ℚ) ^ scheduledInitialMagnitudeExponent E := by
  have hpos : 0 < rationalStateAbsBound E :=
    (show (0 : ℚ) < 2 by norm_num).trans_le
      (rationalStateAbsBound_two_le E)
  exact (positive_rational_lt_two_pow_encodedBitLength hpos).le

/-- The determinant-independent precision computed once for a feasibility
run. -/
def scheduledFeasibilityPrecision {d : ℕ}
    (budget : ℕ) (E : RationalEllipsoidState d) : ℕ :=
  roundedEllipsoidPrecisionSchedule d
    (scheduledInitialDetExponent E)
    (scheduledInitialMagnitudeExponent E) budget

/-- Recursive loop at a fixed precision. -/
def runFixedPrecisionRationalFeasibility {d : ℕ} (p : ℕ)
    (oracle : RationalCentralOracle d) :
    ℕ → RationalEllipsoidState d → RationalFeasibilityResult d
  | 0, E => .exhausted E
  | budget + 1, E =>
      match oracle E with
      | .accept => .accepted E.center
      | .cut a => runFixedPrecisionRationalFeasibility p oracle budget
          (scheduledRoundedEllipsoidCentralUpdate p E a)

/-- Public scheduled runner.  Its precision contains no determinant
evaluation and is unchanged inside the loop. -/
def runScheduledRationalFeasibility {d : ℕ}
    (oracle : RationalCentralOracle d)
    (budget : ℕ) (E : RationalEllipsoidState d) :
    RationalFeasibilityResult d :=
  runFixedPrecisionRationalFeasibility
    (scheduledFeasibilityPrecision budget E) oracle budget E

theorem runFixedPrecisionRationalFeasibility_acceptsOnly {d p : ℕ}
    {Good : (Fin d → ℚ) → Prop} {oracle : RationalCentralOracle d}
    (haccept : RationalCentralOracleAcceptsOnly Good oracle)
    {budget : ℕ} {E : RationalEllipsoidState d} {x : Fin d → ℚ}
    (hrun : runFixedPrecisionRationalFeasibility p oracle budget E =
      .accepted x) : Good x := by
  induction budget generalizing E with
  | zero => simp [runFixedPrecisionRationalFeasibility] at hrun
  | succ budget ih =>
      rw [runFixedPrecisionRationalFeasibility] at hrun
      split at hrun <;> rename_i hresponse
      · cases hrun
        exact haccept E hresponse
      · exact ih hrun

theorem runScheduledRationalFeasibility_acceptsOnly {d : ℕ}
    {Good : (Fin d → ℚ) → Prop} {oracle : RationalCentralOracle d}
    (haccept : RationalCentralOracleAcceptsOnly Good oracle)
    {budget : ℕ} {E : RationalEllipsoidState d} {x : Fin d → ℚ}
    (hrun : runScheduledRationalFeasibility oracle budget E = .accepted x) :
    Good x := by
  exact runFixedPrecisionRationalFeasibility_acceptsOnly haccept
    (by simpa only [runScheduledRationalFeasibility] using hrun)

theorem scheduledRoundedEllipsoidCentralUpdate_contains_point {d p : ℕ}
    (hd : 0 < d) (E : RationalEllipsoidState d) (a : Fin d → ℚ)
    (hdet : Matrix.det E.basis ≠ 0)
    (hp : roundedEllipsoidPrecision
      (rationalEllipsoidCentralUpdate E a) ≤ p)
    {x : Fin d → ℝ} (hcontains : RationalEllipsoidContains E x)
    (ha : a ≠ 0)
    (hcut : finiteDot (fun i ↦ (a i : ℝ))
      (fun i ↦ x i - rationalCenterReal E i) ≤ 0) :
    RationalEllipsoidContains
      (scheduledRoundedEllipsoidCentralUpdate p E a) x := by
  obtain ⟨y, hy, hpoint⟩ := hcontains
  have hb := rationalPulledBackNormal_ne_zero_of_det_ne_zero E a hdet ha
  have hpulled : finiteDot
      (fun j ↦ (rationalPulledBackNormal E a j : ℝ)) y ≤ 0 := by
    rw [← physicalDot_point_sub_center_eq_pulledDot E a y]
    simpa only [hpoint] using hcut
  obtain ⟨y', hy', hpoint'⟩ :=
    scheduledRoundedEllipsoidCentralUpdate_contains
      hd E a hdet hb hp hy hpulled
  exact ⟨y', hy', hpoint'.trans hpoint⟩

theorem scheduledContractionFactor_nonneg {d : ℕ} (hd : 0 < d) :
    0 ≤ 1 - 1 / (32 * (d : ℝ) ^ 3) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (1 : ℝ) ≤ 32 * (d : ℝ) ^ 3 := by
    nlinarith [one_le_pow₀ (n := 3) hdR]
  exact sub_nonneg.mpr
    ((div_le_one (by positivity : (0 : ℝ) < 32 * (d : ℝ) ^ 3)).2 hden)

/-- Target preservation for a fixed-precision run.  The global invariant
discharges the rounding precision at each recursive call. -/
theorem runFixedPrecisionRationalFeasibility_preserves_target_of_exhausted
    {d L K T t : ℕ} (hd : 0 < d)
    {Target : (Fin d → ℝ) → Prop} {oracle : RationalCentralOracle d}
    (hvalid : RationalCentralOracleValid Target oracle)
    {budget : ℕ} {E E' : RationalEllipsoidState d}
    (hInv : ScheduledEllipsoidInvariant d L K t E)
    (hbudget : t + budget ≤ T)
    (hrun : runFixedPrecisionRationalFeasibility
      (roundedEllipsoidPrecisionSchedule d L K T) oracle budget E =
        .exhausted E')
    {x : Fin d → ℝ} (hTarget : Target x)
    (hcontains : RationalEllipsoidContains E x) :
    RationalEllipsoidContains E' x := by
  induction budget generalizing E E' t with
  | zero =>
      simp only [runFixedPrecisionRationalFeasibility] at hrun
      cases hrun
      exact hcontains
  | succ budget ih =>
      rw [runFixedPrecisionRationalFeasibility] at hrun
      split at hrun
      · contradiction
      · rename_i a hresponse
        have hcut := hvalid E a hresponse
        have hb := rationalPulledBackNormal_ne_zero_of_det_ne_zero
          E a hInv.det_ne_zero hcut.1
        have htT : t ≤ T := by omega
        have hadvance := hInv.advance hd a hb htT
        let E₁ := scheduledRoundedEllipsoidCentralUpdate
          (roundedEllipsoidPrecisionSchedule d L K T) E a
        have hInv₁ : ScheduledEllipsoidInvariant d L K (t + 1) E₁ := by
          simpa only [E₁] using hadvance.2
        have hnext := scheduledRoundedEllipsoidCentralUpdate_contains_point
          hd E a hInv.det_ne_zero hadvance.1 hcontains hcut.1
            (hcut.2 x hTarget)
        apply ih hInv₁
        · omega
        · exact hrun
        · exact hnext

theorem runFixedPrecisionRationalFeasibility_det_upper_of_exhausted
    {d L K T t : ℕ} (hd : 0 < d)
    {Target : (Fin d → ℝ) → Prop} {oracle : RationalCentralOracle d}
    (hvalid : RationalCentralOracleValid Target oracle)
    {budget : ℕ} {E E' : RationalEllipsoidState d}
    (hInv : ScheduledEllipsoidInvariant d L K t E)
    (hbudget : t + budget ≤ T)
    (hrun : runFixedPrecisionRationalFeasibility
      (roundedEllipsoidPrecisionSchedule d L K T) oracle budget E =
        .exhausted E') :
    abs ((Matrix.det E'.basis : ℚ) : ℝ) ≤
      (1 - 1 / (32 * (d : ℝ) ^ 3)) ^ budget *
        abs ((Matrix.det E.basis : ℚ) : ℝ) := by
  induction budget generalizing E E' t with
  | zero =>
      simp only [runFixedPrecisionRationalFeasibility] at hrun
      cases hrun
      simp
  | succ budget ih =>
      rw [runFixedPrecisionRationalFeasibility] at hrun
      split at hrun
      · contradiction
      · rename_i a hresponse
        have hcut := hvalid E a hresponse
        have hb := rationalPulledBackNormal_ne_zero_of_det_ne_zero
          E a hInv.det_ne_zero hcut.1
        have htT : t ≤ T := by omega
        have hadvance := hInv.advance hd a hb htT
        let E₁ := scheduledRoundedEllipsoidCentralUpdate
          (roundedEllipsoidPrecisionSchedule d L K T) E a
        have hInv₁ : ScheduledEllipsoidInvariant d L K (t + 1) E₁ := by
          simpa only [E₁] using hadvance.2
        have htail := ih hInv₁ (by omega) hrun
        have hstep := abs_det_scheduledRoundedCentralUpdate_le
          hd E a hInv.det_ne_zero hb hadvance.1
        have hfactor0 := scheduledContractionFactor_nonneg hd
        calc
          abs ((Matrix.det E'.basis : ℚ) : ℝ) ≤
              (1 - 1 / (32 * (d : ℝ) ^ 3)) ^ budget *
                abs ((Matrix.det E₁.basis : ℚ) : ℝ) := htail
          _ ≤ (1 - 1 / (32 * (d : ℝ) ^ 3)) ^ budget *
              ((1 - 1 / (32 * (d : ℝ) ^ 3)) *
                abs ((Matrix.det E.basis : ℚ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hstep (pow_nonneg hfactor0 _)
          _ = (1 - 1 / (32 * (d : ℝ) ^ 3)) ^ (budget + 1) *
              abs ((Matrix.det E.basis : ℚ) : ℝ) := by
            rw [pow_succ]
            ring

theorem scheduledInitialInvariant {d : ℕ}
    (E : RationalEllipsoidState d) (hdet : Matrix.det E.basis ≠ 0) :
    ScheduledEllipsoidInvariant d (scheduledInitialDetExponent E)
      (scheduledInitialMagnitudeExponent E) 0 E := by
  refine ⟨hdet, ?_, ?_⟩
  · simpa using scheduledInitialDetExponent_lower E hdet
  · simpa using scheduledInitialMagnitudeExponent_upper E

theorem runScheduledRationalFeasibility_preserves_target_of_exhausted
    {d : ℕ} (hd : 0 < d)
    {Target : (Fin d → ℝ) → Prop} {oracle : RationalCentralOracle d}
    (hvalid : RationalCentralOracleValid Target oracle)
    {budget : ℕ} {E E' : RationalEllipsoidState d}
    (hdet : Matrix.det E.basis ≠ 0)
    (hrun : runScheduledRationalFeasibility oracle budget E = .exhausted E')
    {x : Fin d → ℝ} (hTarget : Target x)
    (hcontains : RationalEllipsoidContains E x) :
    RationalEllipsoidContains E' x := by
  let L := scheduledInitialDetExponent E
  let K := scheduledInitialMagnitudeExponent E
  have hInv : ScheduledEllipsoidInvariant d L K 0 E := by
    simpa only [L, K] using scheduledInitialInvariant E hdet
  apply runFixedPrecisionRationalFeasibility_preserves_target_of_exhausted
    (L := L) (K := K) (T := budget) (t := 0) (budget := budget)
      (E := E) (E' := E') hd hvalid hInv (by omega)
  · simpa only [runScheduledRationalFeasibility,
      scheduledFeasibilityPrecision, L, K] using hrun
  · exact hTarget
  · exact hcontains

theorem runScheduledRationalFeasibility_det_upper_of_exhausted
    {d : ℕ} (hd : 0 < d)
    {Target : (Fin d → ℝ) → Prop} {oracle : RationalCentralOracle d}
    (hvalid : RationalCentralOracleValid Target oracle)
    {budget : ℕ} {E E' : RationalEllipsoidState d}
    (hdet : Matrix.det E.basis ≠ 0)
    (hrun : runScheduledRationalFeasibility oracle budget E = .exhausted E') :
    abs ((Matrix.det E'.basis : ℚ) : ℝ) ≤
      (1 - 1 / (32 * (d : ℝ) ^ 3)) ^ budget *
        abs ((Matrix.det E.basis : ℚ) : ℝ) := by
  let L := scheduledInitialDetExponent E
  let K := scheduledInitialMagnitudeExponent E
  have hInv : ScheduledEllipsoidInvariant d L K 0 E := by
    simpa only [L, K] using scheduledInitialInvariant E hdet
  apply runFixedPrecisionRationalFeasibility_det_upper_of_exhausted
    (L := L) (K := K) (T := budget) (t := 0) (budget := budget)
      (E := E) (E' := E') hd hvalid hInv (by omega)
  simpa only [runScheduledRationalFeasibility,
    scheduledFeasibilityPrecision, L, K] using hrun

theorem runScheduledRationalFeasibility_not_exhausted_of_inner_cross
    {d M : ℕ} (hd : 0 < d)
    {Target : (Fin d → ℝ) → Prop} {oracle : RationalCentralOracle d}
    (hvalid : RationalCentralOracleValid Target oracle)
    (E : RationalEllipsoidState d)
    (hdet : Matrix.det E.basis ≠ 0)
    {z : Fin d → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hdyadic : Nat.factorial d * abs ((Matrix.det E.basis : ℚ) : ℝ) *
      (1 / 2 : ℝ) ^ M < r ^ d)
    (hTargetPlus : ∀ k, Target
      (fun i ↦ z i + if i = k then r else 0))
    (hTargetMinus : ∀ k, Target
      (fun i ↦ z i - if i = k then r else 0))
    (hEplus : ∀ k, RationalEllipsoidContains E
      (fun i ↦ z i + if i = k then r else 0))
    (hEminus : ∀ k, RationalEllipsoidContains E
      (fun i ↦ z i - if i = k then r else 0))
    (E' : RationalEllipsoidState d) :
    runScheduledRationalFeasibility oracle (32 * d ^ 3 * M) E ≠
      .exhausted E' := by
  intro hrun
  have hplus : ∀ k, RationalEllipsoidContains E'
      (fun i ↦ z i + if i = k then r else 0) := by
    intro k
    exact runScheduledRationalFeasibility_preserves_target_of_exhausted
      hd hvalid hdet hrun (hTargetPlus k) (hEplus k)
  have hminus : ∀ k, RationalEllipsoidContains E'
      (fun i ↦ z i - if i = k then r else 0) := by
    intro k
    exact runScheduledRationalFeasibility_preserves_target_of_exhausted
      hd hvalid hdet hrun (hTargetMinus k) (hEminus k)
  have hlower := rationalEllipsoid_storedDet_lower_of_ball_endpoints
    E' hr (fun k ↦ hplus k) (fun k ↦ hminus k)
  have hupper := runScheduledRationalFeasibility_det_upper_of_exhausted
    hd hvalid hdet hrun
  have hfactor := roundedContractionFactor_pow_budget_le_half_pow
    (d := d) (M := M) hd
  have hdetUpper : abs ((Matrix.det E'.basis : ℚ) : ℝ) ≤
      (1 / 2 : ℝ) ^ M * abs ((Matrix.det E.basis : ℚ) : ℝ) :=
    hupper.trans (mul_le_mul_of_nonneg_right hfactor (abs_nonneg _))
  have hsandwich : r ^ d ≤
      Nat.factorial d * abs ((Matrix.det E.basis : ℚ) : ℝ) *
        (1 / 2 : ℝ) ^ M := by
    calc
      r ^ d ≤ Nat.factorial d *
          abs ((Matrix.det E'.basis : ℚ) : ℝ) := hlower
      _ ≤ Nat.factorial d *
          ((1 / 2 : ℝ) ^ M *
            abs ((Matrix.det E.basis : ℚ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hdetUpper (Nat.cast_nonneg _)
      _ = Nat.factorial d * abs ((Matrix.det E.basis : ℚ) : ℝ) *
          (1 / 2 : ℝ) ^ M := by ring
  exact (not_lt_of_ge hsandwich) hdyadic

/-- Ball specialization used by the determinant-independent epigraph
feasibility call. -/
theorem runScheduledRationalFeasibility_ball_accepts
    {d : ℕ} (hd : 0 < d)
    {Target : (Fin d → ℝ) → Prop} {Good : (Fin d → ℚ) → Prop}
    {oracle : RationalCentralOracle d}
    (hvalid : RationalCentralOracleValid Target oracle)
    (haccept : RationalCentralOracleAcceptsOnly Good oracle)
    (c : Fin d → ℚ) {R r : ℚ} (hR : 0 < R) (hr : 0 < r)
    {z : Fin d → ℝ}
    (hTargetPlus : ∀ k, Target
      (fun i ↦ z i + if i = k then (r : ℝ) else 0))
    (hTargetMinus : ∀ k, Target
      (fun i ↦ z i - if i = k then (r : ℝ) else 0))
    (houterPlus : ∀ k, finiteNormSq
      (fun i ↦ (z i + if i = k then (r : ℝ) else 0) - (c i : ℝ)) ≤
        (R : ℝ) ^ 2)
    (houterMinus : ∀ k, finiteNormSq
      (fun i ↦ (z i - if i = k then (r : ℝ) else 0) - (c i : ℝ)) ≤
        (R : ℝ) ^ 2) :
    ∃ x : Fin d → ℚ,
      runScheduledRationalFeasibility oracle
          (32 * d ^ 3 * rationalBallDyadicExponent d R r)
          (rationalBallEllipsoid d c R) = .accepted x ∧ Good x := by
  let E := rationalBallEllipsoid d c R
  let budget := 32 * d ^ 3 * rationalBallDyadicExponent d R r
  let result := runScheduledRationalFeasibility oracle budget E
  cases hresult : result with
  | accepted x =>
      refine ⟨x, ?_, ?_⟩
      · simpa only [result, budget, E] using hresult
      · exact runScheduledRationalFeasibility_acceptsOnly haccept
          (by simpa only [result, budget, E] using hresult)
  | exhausted E' =>
      exfalso
      apply runScheduledRationalFeasibility_not_exhausted_of_inner_cross
        hd hvalid E
          (by
            dsimp only [E]
            rw [det_rationalBallEllipsoid]
            exact pow_ne_zero _ hR.ne')
          (hr := Rat.cast_nonneg.mpr hr.le)
          (rationalBallEllipsoid_dyadic_budget hd c hR hr)
          hTargetPlus hTargetMinus
      · intro k
        exact rationalBallEllipsoid_contains c hR (houterPlus k)
      · intro k
        exact rationalBallEllipsoid_contains c hR (houterMinus k)
      · simpa only [result, budget, E] using hresult

end BeyondBethe
