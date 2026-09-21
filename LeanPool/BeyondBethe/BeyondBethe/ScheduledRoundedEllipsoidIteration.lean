/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.ScheduledRoundedEllipsoid
import Mathlib.Tactic

/-! # Scheduled Rounded Ellipsoid Iteration -/

namespace BeyondBethe

/-!
# Iteration of the determinant-independent schedule

The theorem in this file is the bridge from the semantic one-step precision
requirement to a genuine implementation.  One precision is computed from the
initial determinant exponent, initial magnitude exponent, and total cut
budget.  Induction proves that it is sufficient at every reachable regular
state.  No determinant is evaluated by the scheduled iteration.
-/

def scheduledRoundedEllipsoidIterate {d : ℕ} (p : ℕ) :
    RationalEllipsoidState d → List (Fin d → ℚ) → RationalEllipsoidState d
  | E, [] => E
  | E, a :: cuts => scheduledRoundedEllipsoidIterate p
      (scheduledRoundedEllipsoidCentralUpdate p E a) cuts

def ScheduledCutSequenceRegular {d : ℕ} (p : ℕ) :
    RationalEllipsoidState d → List (Fin d → ℚ) → Prop
  | _, [] => True
  | E, a :: cuts =>
      rationalPulledBackNormal E a ≠ 0 ∧
        ScheduledCutSequenceRegular p
          (scheduledRoundedEllipsoidCentralUpdate p E a) cuts

theorem dyadicMesh_add_two_step (L t : ℕ) :
    dyadicMesh (L + 2 * (t + 1)) =
      (1 / 4 : ℚ) * dyadicMesh (L + 2 * t) := by
  rw [dyadicMesh_add_two_mul, dyadicMesh_add_two_mul, pow_succ]
  ring

private theorem scheduled_state_step_two_pow {d K t : ℕ} (hd : 0 < d)
    (E : RationalEllipsoidState d) (a : Fin d → ℚ) (p : ℕ)
    (hb : rationalPulledBackNormal E a ≠ 0)
    (hM : rationalStateAbsBound E ≤
      (2 : ℚ) ^ (K + t * (6 + 3 * d))) :
    rationalStateAbsBound (scheduledRoundedEllipsoidCentralUpdate p E a) ≤
      (2 : ℚ) ^ (K + (t + 1) * (6 + 3 * d)) := by
  have hstep := rationalStateAbsBound_scheduledCentralUpdate_le
    (p := p) hd E a hb
  have hfactor := roundedEllipsoidStateGrowthFactor_le_two_pow d
  have hstate0 : 0 ≤ rationalStateAbsBound E := by
    linarith [rationalStateAbsBound_two_le E]
  calc
    rationalStateAbsBound (scheduledRoundedEllipsoidCentralUpdate p E a) ≤
        (42 * d ^ 3 : ℚ) * rationalStateAbsBound E := hstep
    _ ≤ (2 : ℚ) ^ (6 + 3 * d) *
        (2 : ℚ) ^ (K + t * (6 + 3 * d)) :=
      mul_le_mul hfactor hM hstate0 (by positivity)
    _ = (2 : ℚ) ^ (K + (t + 1) * (6 + 3 * d)) := by
      rw [← pow_add]
      congr 1
      ring

/-- The three quantitative facts carried by a scheduled run after `t` cuts. -/
structure ScheduledEllipsoidInvariant (d L K t : ℕ)
    (E : RationalEllipsoidState d) : Prop where
  det_ne_zero : Matrix.det E.basis ≠ 0
  det_lower : dyadicMesh (L + 2 * t) ≤ abs (Matrix.det E.basis)
  magnitude : rationalStateAbsBound E ≤
    (2 : ℚ) ^ (K + t * (6 + 3 * d))

/-- The schedule is sufficient for the next cut, and the next state satisfies
the invariant at time `t+1`. -/
theorem ScheduledEllipsoidInvariant.advance
    {d L K T t : ℕ} (hd : 0 < d)
    {E : RationalEllipsoidState d}
    (hE : ScheduledEllipsoidInvariant d L K t E)
    (a : Fin d → ℚ) (hb : rationalPulledBackNormal E a ≠ 0)
    (htT : t ≤ T) :
    let P := roundedEllipsoidPrecisionSchedule d L K T
    let U := rationalEllipsoidCentralUpdate E a
    let E₁ := scheduledRoundedEllipsoidCentralUpdate P E a
    roundedEllipsoidPrecision U ≤ P ∧
      ScheduledEllipsoidInvariant d L K (t + 1) E₁ := by
  let P := roundedEllipsoidPrecisionSchedule d L K T
  let U := rationalEllipsoidCentralUpdate E a
  let E₁ := scheduledRoundedEllipsoidCentralUpdate P E a
  have hsemantic0 := rationalEllipsoidCentralUpdate_precision_upper
    hd E a hb hE.det_lower hE.magnitude
  have hsemantic : roundedEllipsoidPrecision U ≤
      roundedEllipsoidNextPrecisionBound d L K t := by
    simpa only [U, roundedEllipsoidNextPrecisionBound] using hsemantic0
  have hp : roundedEllipsoidPrecision U ≤ P :=
    hsemantic.trans (roundedEllipsoidNextPrecisionBound_le_schedule htT)
  have hdet₁ : Matrix.det E₁.basis ≠ 0 := by
    dsimp only [E₁, P, U] at hp ⊢
    exact det_scheduledRoundedEllipsoidCentralUpdate_ne_zero
      hd E a hE.det_ne_zero hb hp
  have hquarter := quarter_abs_det_le_scheduledRoundedCentralUpdate_rat
    hd E a hE.det_ne_zero hb hp
  have hdetLower₁ : dyadicMesh (L + 2 * (t + 1)) ≤
      abs (Matrix.det E₁.basis) := by
    rw [dyadicMesh_add_two_step]
    exact (mul_le_mul_of_nonneg_left hE.det_lower (by norm_num)).trans
      (by simpa only [E₁, P] using hquarter)
  have hM₁ : rationalStateAbsBound E₁ ≤
      (2 : ℚ) ^ (K + (t + 1) * (6 + 3 * d)) := by
    dsimp only [E₁, P]
    exact scheduled_state_step_two_pow hd E a _ hb hE.magnitude
  exact ⟨hp, hdet₁, hdetLower₁, hM₁⟩

/-- One fixed precision, computed before the run, dominates every semantic
precision requirement and preserves the determinant and magnitude invariants
through an arbitrary regular cut sequence of the budgeted length. -/
theorem scheduledRoundedEllipsoidIterate_invariants
    {d L K T t : ℕ} (hd : 0 < d)
    (E : RationalEllipsoidState d)
    (hdet : Matrix.det E.basis ≠ 0)
    (hdetLower : dyadicMesh (L + 2 * t) ≤ abs (Matrix.det E.basis))
    (hM : rationalStateAbsBound E ≤
      (2 : ℚ) ^ (K + t * (6 + 3 * d)))
    (cuts : List (Fin d → ℚ))
    (hregular : ScheduledCutSequenceRegular
      (roundedEllipsoidPrecisionSchedule d L K T) E cuts)
    (hbudget : t + cuts.length ≤ T) :
    let E' := scheduledRoundedEllipsoidIterate
      (roundedEllipsoidPrecisionSchedule d L K T) E cuts
    Matrix.det E'.basis ≠ 0 ∧
      dyadicMesh (L + 2 * (t + cuts.length)) ≤
        abs (Matrix.det E'.basis) ∧
      rationalStateAbsBound E' ≤
        (2 : ℚ) ^ (K + (t + cuts.length) * (6 + 3 * d)) := by
  induction cuts generalizing E t with
  | nil =>
      simpa [scheduledRoundedEllipsoidIterate] using
        And.intro hdet (And.intro hdetLower hM)
  | cons a cuts ih =>
      let P := roundedEllipsoidPrecisionSchedule d L K T
      let E₁ := scheduledRoundedEllipsoidCentralUpdate P E a
      have hb : rationalPulledBackNormal E a ≠ 0 := hregular.1
      have htT : t ≤ T := by omega
      let hInv : ScheduledEllipsoidInvariant d L K t E :=
        ⟨hdet, hdetLower, hM⟩
      have hadvance := hInv.advance hd a hb htT
      have hInv₁ : ScheduledEllipsoidInvariant d L K (t + 1) E₁ := by
        simpa only [E₁, P] using hadvance.2
      have hbudgetTail : (t + 1) + cuts.length ≤ T := by
        simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hbudget
      have htail := ih (E := E₁) (t := t + 1) hInv₁.det_ne_zero
        hInv₁.det_lower hInv₁.magnitude
        hregular.2 hbudgetTail
      have hindex : t + 1 + cuts.length = t + (cuts.length + 1) := by
        omega
      simpa only [scheduledRoundedEllipsoidIterate, E₁, P,
        List.length_cons, hindex] using htail

/-- Initial-state specialization of the scheduled invariants. -/
theorem scheduledRoundedEllipsoidIterate_from_initial
    {d L K T : ℕ} (hd : 0 < d)
    (E : RationalEllipsoidState d)
    (hdet : Matrix.det E.basis ≠ 0)
    (hdetLower : dyadicMesh L ≤ abs (Matrix.det E.basis))
    (hM : rationalStateAbsBound E ≤ (2 : ℚ) ^ K)
    (cuts : List (Fin d → ℚ))
    (hregular : ScheduledCutSequenceRegular
      (roundedEllipsoidPrecisionSchedule d L K T) E cuts)
    (hbudget : cuts.length ≤ T) :
    let E' := scheduledRoundedEllipsoidIterate
      (roundedEllipsoidPrecisionSchedule d L K T) E cuts
    Matrix.det E'.basis ≠ 0 ∧
      dyadicMesh (L + 2 * cuts.length) ≤ abs (Matrix.det E'.basis) ∧
      rationalStateAbsBound E' ≤
        (2 : ℚ) ^ (K + cuts.length * (6 + 3 * d)) := by
  simpa using scheduledRoundedEllipsoidIterate_invariants
    (L := L) (K := K) (T := T) (t := 0) hd E hdet
      (by simpa using hdetLower) (by simpa using hM) cuts hregular
      (by omega)

end BeyondBethe
