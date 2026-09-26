/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.RoundedFeasibility
public import LeanPool.BeyondBethe.BeyondBethe.RationalEncodingBounds
public import Mathlib.Tactic

/-! # Rounded Feasibility Bit Bounds -/

@[expose] public section

namespace BeyondBethe

/-!
# Traces and size invariants for rounded feasibility

The executable runner is recursive on a natural budget.  This file exposes
the exact list of cuts it actually executes and connects that trace to the
iteration bounds.  No feasibility assumption is needed for the size bounds;
oracle validity supplies only the nonzero-cut invariant.
-/

/-- Records the cuts encountered by the adaptive rounded feasibility run, stopping on acceptance
or budget exhaustion. -/
def roundedRationalFeasibilityCuts {d : ℕ}
    (oracle : RationalCentralOracle d) :
    ℕ → RationalEllipsoidState d → List (Fin d → ℚ)
  | 0, _ => []
  | budget + 1, E =>
      match oracle E with
      | .accept => []
      | .cut a => a :: roundedRationalFeasibilityCuts oracle budget
          (adaptiveRoundedEllipsoidCentralUpdate E a)

theorem roundedRationalFeasibilityCuts_length_le {d : ℕ}
    (oracle : RationalCentralOracle d) (budget : ℕ)
    (E : RationalEllipsoidState d) :
    (roundedRationalFeasibilityCuts oracle budget E).length ≤ budget := by
  induction budget generalizing E with
  | zero => simp [roundedRationalFeasibilityCuts]
  | succ budget ih =>
      rw [roundedRationalFeasibilityCuts]
      split
      · simp
      · simp only [List.length_cons]
        exact Nat.succ_le_succ (ih _)

theorem adaptiveRoundedEllipsoidIterate_feasibilityCuts_terminal {d : ℕ}
    (oracle : RationalCentralOracle d) (budget : ℕ)
    (E : RationalEllipsoidState d) :
    match runRoundedRationalFeasibility oracle budget E with
    | .accepted x =>
        (adaptiveRoundedEllipsoidIterate E
          (roundedRationalFeasibilityCuts oracle budget E)).center = x
    | .exhausted E' =>
        adaptiveRoundedEllipsoidIterate E
          (roundedRationalFeasibilityCuts oracle budget E) = E' := by
  induction budget generalizing E with
  | zero => simp [runRoundedRationalFeasibility,
      roundedRationalFeasibilityCuts, adaptiveRoundedEllipsoidIterate]
  | succ budget ih =>
      cases hresponse : oracle E with
      | accept =>
          simp [runRoundedRationalFeasibility,
            roundedRationalFeasibilityCuts, hresponse,
            adaptiveRoundedEllipsoidIterate]
      | cut a =>
          let E' := adaptiveRoundedEllipsoidCentralUpdate E a
          have htail := ih E'
          cases hrun : runRoundedRationalFeasibility oracle budget E' with
          | accepted x =>
              rw [hrun] at htail
              simpa only [runRoundedRationalFeasibility,
                roundedRationalFeasibilityCuts, hresponse,
                adaptiveRoundedEllipsoidIterate, E', hrun] using htail
          | exhausted U =>
              rw [hrun] at htail
              simpa only [runRoundedRationalFeasibility,
                roundedRationalFeasibilityCuts, hresponse,
                adaptiveRoundedEllipsoidIterate, E', hrun] using htail

theorem roundedRationalFeasibilityCuts_regular {d : ℕ}
    (hd : 0 < d) {K : (Fin d → ℝ) → Prop}
    {oracle : RationalCentralOracle d}
    (hvalid : RationalCentralOracleValid K oracle)
    (budget : ℕ) (E : RationalEllipsoidState d)
    (hdet : Matrix.det E.basis ≠ 0) :
    AdaptiveCutSequenceRegular E
      (roundedRationalFeasibilityCuts oracle budget E) := by
  induction budget generalizing E with
  | zero => simp [roundedRationalFeasibilityCuts,
      AdaptiveCutSequenceRegular]
  | succ budget ih =>
      rw [roundedRationalFeasibilityCuts]
      split <;> rename_i hresponse
      · simp [AdaptiveCutSequenceRegular]
      · have ha := (hvalid E _ hresponse).1
        have hb := rationalPulledBackNormal_ne_zero_of_det_ne_zero
          E _ hdet ha
        have hdet' := det_adaptiveRoundedEllipsoidCentralUpdate_ne_zero
          hd E _ hdet hb
        exact ⟨hb, ih _ hdet'⟩

/-- Every terminal state of a valid rounded run has a trace of at most the
budgeted length and satisfies the determinant, magnitude, and precision
invariants proved for abstract regular traces. -/
theorem runRoundedRationalFeasibility_terminal_invariants {d L K : ℕ}
    (hd : 0 < d) {Target : (Fin d → ℝ) → Prop}
    {oracle : RationalCentralOracle d}
    (hvalid : RationalCentralOracleValid Target oracle)
    (budget : ℕ) (E : RationalEllipsoidState d)
    (hdet : Matrix.det E.basis ≠ 0)
    (hdetLower : dyadicMesh L ≤ abs (Matrix.det E.basis))
    (hM : rationalStateAbsBound E ≤ (2 : ℚ) ^ K) :
    let cuts := roundedRationalFeasibilityCuts oracle budget E
    cuts.length ≤ budget ∧
      AdaptiveCutSequenceRegular E cuts ∧
      dyadicMesh (L + 2 * cuts.length) ≤
        abs (Matrix.det (adaptiveRoundedEllipsoidIterate E cuts).basis) ∧
      rationalStateAbsBound (adaptiveRoundedEllipsoidIterate E cuts) ≤
        (2 : ℚ) ^ roundedEllipsoidStateMagnitudeExponent
          d K cuts.length ∧
      roundedEllipsoidPrecision (adaptiveRoundedEllipsoidIterate E cuts) ≤
        (L + 2 * cuts.length) +
          roundedEllipsoidDenominatorExponent d
            (roundedEllipsoidMagnitudeExponent d K cuts.length) + 2 := by
  let cuts := roundedRationalFeasibilityCuts oracle budget E
  have hlen : cuts.length ≤ budget :=
    roundedRationalFeasibilityCuts_length_le oracle budget E
  have hregular : AdaptiveCutSequenceRegular E cuts :=
    roundedRationalFeasibilityCuts_regular hd hvalid budget E hdet
  have hMbasis : rationalMatrixAbsBound E.basis ≤ (2 : ℚ) ^ K :=
    (rationalMatrixAbsBound_le_rationalStateAbsBound E).trans hM
  exact ⟨hlen, hregular,
    adaptiveRoundedEllipsoidIterate_dyadic_det_lower
      hd E hdet hdetLower cuts hregular,
    adaptiveRoundedEllipsoidIterate_two_pow_state_magnitude_upper
      hd E hM cuts hregular,
    adaptiveRoundedEllipsoidIterate_precision_upper
      hd E hdet hdetLower hMbasis cuts hregular⟩

/-- Every exact central update that is actually requested by a valid run uses
at most the stated polynomial precision.  The decomposition identifies the
cut and the trace prefix before it. -/
theorem roundedRationalFeasibilityCuts_next_precision_upper
    {d L K : ℕ} (hd : 0 < d)
    {Target : (Fin d → ℝ) → Prop}
    {oracle : RationalCentralOracle d}
    (hvalid : RationalCentralOracleValid Target oracle)
    (budget : ℕ) (E : RationalEllipsoidState d)
    (hdet : Matrix.det E.basis ≠ 0)
    (hdetLower : dyadicMesh L ≤ abs (Matrix.det E.basis))
    (hM : rationalStateAbsBound E ≤ (2 : ℚ) ^ K)
    (pre suffix : List (Fin d → ℚ)) (a : Fin d → ℚ)
    (htrace : roundedRationalFeasibilityCuts oracle budget E =
      pre ++ a :: suffix) :
    roundedEllipsoidPrecision
        (rationalEllipsoidCentralUpdate
          (adaptiveRoundedEllipsoidIterate E pre) a) ≤
      roundedEllipsoidNextPrecisionBound d L K pre.length := by
  have hregular := roundedRationalFeasibilityCuts_regular
    hd hvalid budget E hdet
  rw [htrace] at hregular
  have hpre := AdaptiveCutSequenceRegular.prefix_and_next
    E pre suffix a hregular
  exact adaptiveRoundedEllipsoidIterate_next_precision_upper
    hd E hdet hdetLower hM pre hpre.1 a hpre.2

/-- The stored state immediately after every executed cut has a fully
explicit encoding-length bound. -/
theorem roundedRationalFeasibilityCuts_next_state_encodedBitLength_le
    {d L K : ℕ} (hd : 0 < d)
    {Target : (Fin d → ℝ) → Prop}
    {oracle : RationalCentralOracle d}
    (hvalid : RationalCentralOracleValid Target oracle)
    (budget : ℕ) (E : RationalEllipsoidState d)
    (hdet : Matrix.det E.basis ≠ 0)
    (hdetLower : dyadicMesh L ≤ abs (Matrix.det E.basis))
    (hM : rationalStateAbsBound E ≤ (2 : ℚ) ^ K)
    (pre suffix : List (Fin d → ℚ)) (a : Fin d → ℚ)
    (htrace : roundedRationalFeasibilityCuts oracle budget E =
      pre ++ a :: suffix) :
    rationalEllipsoidStateEncodedBitLength
        (adaptiveRoundedEllipsoidCentralUpdate
          (adaptiveRoundedEllipsoidIterate E pre) a) ≤
      6 + d * (20 + 4 *
          roundedEllipsoidStateMagnitudeExponent d K (pre.length + 1) +
          8 * roundedEllipsoidNextPrecisionBound d L K pre.length) +
        2 * d + d ^ 2 * (100 + 4 *
          roundedEllipsoidStateMagnitudeExponent d K (pre.length + 1) +
          8 * roundedEllipsoidNextPrecisionBound d L K pre.length +
          32 * d) := by
  have hregular := roundedRationalFeasibilityCuts_regular
    hd hvalid budget E hdet
  rw [htrace] at hregular
  have hpre := AdaptiveCutSequenceRegular.prefix_and_next
    E pre suffix a hregular
  have hprea := AdaptiveCutSequenceRegular.append_singleton
    E pre a hpre.1 hpre.2
  have hstate :=
    adaptiveRoundedEllipsoidIterate_two_pow_state_magnitude_upper
      hd E hM (pre ++ [a]) hprea
  have hstate' :
      rationalStateAbsBound
          (adaptiveRoundedEllipsoidCentralUpdate
            (adaptiveRoundedEllipsoidIterate E pre) a) ≤
        (2 : ℚ) ^
          roundedEllipsoidStateMagnitudeExponent d K (pre.length + 1) := by
    rw [adaptiveRoundedEllipsoidIterate_append] at hstate
    simpa only [adaptiveRoundedEllipsoidIterate, List.length_append,
      List.length_singleton, Nat.add_comm] using hstate
  have hp := roundedRationalFeasibilityCuts_next_precision_upper
    hd hvalid budget E hdet hdetLower hM pre suffix a htrace
  exact adaptiveRoundedEllipsoid_state_encodedBitLength_le hd
    (rationalEllipsoidCentralUpdate
      (adaptiveRoundedEllipsoidIterate E pre) a) hstate' hp

end BeyondBethe
