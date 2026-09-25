/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Lift
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Hoare
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.PairValidate.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.PairValidate.Internal

/-!
# Validate paired machine inputs

`pairValidateTM` is a total finite-state recognizer for the image of the
library's self-delimiting `pair` codec. It rejects every malformed outer input
and runs in exactly the generic scanner budget `n + 2`.

This complements `pairSplitCoreTM`: validate first when arbitrary input strings
need rejecting semantics, then rewind and use the canonical splitter to stage
the two decoded components.
-/


@[expose] public section

namespace Complexity

/-- Decoder-facing characterization of membership in `validPairEncoding`. -/
theorem mem_validPairEncoding_iff (bits : List Bool) :
    bits ∈ validPairEncoding ↔ (unpair? bits).isSome = true :=
  Iff.rfl

/-- Extensional characterization: valid encodings are exactly canonical
encodings of some pair of Boolean strings. -/
theorem mem_validPairEncoding_iff_exists_pair (bits : List Bool) :
    bits ∈ validPairEncoding ↔ ∃ x y, bits = pair x y := by
  constructor
  · intro hmem
    change (unpair? bits).isSome = true at hmem
    cases hdecode : unpair? bits with
    | none => simp [hdecode] at hmem
    | some decoded =>
        obtain ⟨x, y⟩ := decoded
        exact ⟨x, y, eq_pair_of_unpair?_eq_some hdecode⟩
  · rintro ⟨x, y, rfl⟩
    simp [validPairEncoding]

/-- Failure of the partial decoder is exactly nonmembership in the valid-pair
language. -/
theorem not_mem_validPairEncoding_iff (bits : List Bool) :
    bits ∉ validPairEncoding ↔ unpair? bits = none := by
  cases hdecode : unpair? bits <;> simp [validPairEncoding, hdecode]

/-- Every canonical `pair` is a valid pair encoding. -/
@[simp] theorem pair_mem_validPairEncoding (x y : List Bool) :
    pair x y ∈ validPairEncoding := by
  simp [validPairEncoding]

namespace TM

/-- The pair-validator fold accepts exactly when the canonical decoder succeeds. -/
theorem pairValidateAccept_fold_eq_true_iff (bits : List Bool) :
    pairValidateAccept (bits.foldl pairValidateStep .next) = true ↔
      (unpair? bits).isSome = true :=
  pairValidateAccept_fold_eq_true_iff_internal bits

/-- The finite-state pair validator decides `validPairEncoding` in linear time. -/
theorem pairValidateTM_decidesInTime :
    pairValidateTM.DecidesInTime validPairEncoding (fun n => n + 2) :=
  pairValidateTM_decidesInTime_internal

/-- Adding arbitrary unused work tapes preserves the validator's language and
exact linear time bound. This is the form used by larger machine pipelines. -/
theorem pairValidateTM_lift_decidesInTime (workTapes : ℕ) :
    (pairValidateTM.liftTM workTapes).DecidesInTime
      validPairEncoding (fun n => n + 2) :=
  liftTM_decidesInTime pairValidateTM workTapes pairValidateTM_decidesInTime

/-- Frame-rich initialized specification for the lifted validator. Besides the
verdict, it exposes the read-only input cells, head bounds, well-formedness of
all tapes, and the fact that every added work tape is parked and blank. These
are the seams needed by `ifTM` and a subsequent input rewind. -/
theorem pairValidateTM_lift_hoareTime (workTapes : ℕ) (bits : List Bool) :
    (pairValidateTM.liftTM workTapes).HoareTime
      (fun inp work out =>
        inp = Tape.init (bits.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧
        out = Tape.init [])
      (fun inp work out =>
        AllTapesWF inp work out ∧
        inp.cells = (Tape.init (bits.map Γ.ofBool)).cells ∧
        inp.head ≤ bits.length + 2 ∧
        (∀ i, work i = (Tape.init []).move Dir3.right) ∧
        out.head ≤ bits.length + 2 ∧
        (bits ∈ validPairEncoding → out.cells 1 = Γ.one) ∧
        (bits ∉ validPairEncoding → out.cells 1 = Γ.zero))
      (bits.length + 2) :=
  pairValidateTM_lift_hoareTime_internal workTapes bits

end TM

end Complexity
