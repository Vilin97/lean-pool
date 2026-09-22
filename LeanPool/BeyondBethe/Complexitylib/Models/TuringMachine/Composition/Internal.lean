/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Composition.Internal.FirstPhase
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Composition.Internal.Tail
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.OutputBounds

/-!
# Sequential composition correctness — proof internals

This module connects the first function computation's placed raw-output
boundary to the normalization tail. It derives coarse monotone time bounds for
both function composition and preprocessing followed by a language decider.
-/


public section

namespace Complexity

namespace TM

variable {nf ng : ℕ}

/-- Internal correctness theorem for the executable sequential function
composition machine. -/
theorem compositionTM_computesInTime_internal
    {tmF : TM nf} {tmG : TM ng}
    {f g : List Bool → List Bool} {TF TG : ℕ → ℕ}
    (hF : tmF.ComputesInTime f TF)
    (hG : tmG.ComputesInTime g TG)
    (hmono : Monotone TG) :
    (compositionTM tmF tmG).ComputesInTime (g ∘ f)
      (fun n => 4 * TF n + 11 + TG (TF n)) := by
  intro x
  obtain ⟨C, t, ht, hreachF, hhaltF, hrawOutput, hrawHead,
      hvirtual, hscratch, hinputInv, hinputHead, hworkBoundary,
      houtputParked⟩ :=
    compositionFirstTM_boundary_internal tmF ng hF x
  let boundaryInput := transitionInput C.input
  let boundaryWork : Fin (compositionTapeCount nf ng) → Tape :=
    fun i => transitionTape (C.work i)
  let boundaryOutput := transitionTape C.output
  have htail := compositionTailTM_hoareTime_internal (nf := nf)
    tmG hG (f x) (TF x.length + 1)
  obtain ⟨D, u, hu, hreachTail, hhaltTail, houtTail⟩ :=
    htail boundaryInput boundaryWork boundaryOutput (by
      refine ⟨hrawOutput, (hworkBoundary _).1, ?_, hvirtual, hscratch,
        houtputParked, hinputInv, hinputHead, ?_⟩
      · dsimp only [boundaryWork]
        omega
      · intro i
        exact hworkBoundary (compositionPrefixIdx nf ng i))
  let first := compositionFirstTM tmF ng
  let tail := compositionTailTM nf ng tmG
  let final := phase2Wrap first tail D
  refine ⟨final, t + 1 + u, ?_, ?_, ?_, ?_⟩
  · have hlength : (f x).length ≤ TF x.length := hF.output_length_le x
    have hgBound : TG (f x).length ≤ TG (TF x.length) := hmono hlength
    have hu' : u ≤ TF x.length + 1 + 2 * (f x).length + 9 + TG (f x).length := by
      omega
    change t + 1 + u ≤ 4 * TF x.length + 11 + TG (TF x.length)
    omega
  · have hreach := seqTM_reachesIn_of_reachesIn first tail
      hreachF hhaltF hreachTail
    simpa [compositionTM, first, tail, final, boundaryInput, boundaryWork,
      boundaryOutput] using! hreach
  · show (compositionTM tmF tmG).halted final
    simpa [compositionTM, first, tail, final] using!
      (phase2Wrap_halted_iff first tail D).2 hhaltTail
  · simpa [final, phase2Wrap, Function.comp_apply] using! houtTail

/-- Internal correctness theorem for deterministic preprocessing followed by a
language decider. -/
theorem compositionTM_decidesInTime_preimage_internal
    {tmF : TM nf} {tmG : TM ng}
    {f : List Bool → List Bool} {L : Language} {TF TG : ℕ → ℕ}
    (hF : tmF.ComputesInTime f TF)
    (hG : tmG.DecidesInTime L TG)
    (hmono : Monotone TG) :
    (compositionTM tmF tmG).DecidesInTime (f ⁻¹' L)
      (fun n => 4 * TF n + 11 + TG (TF n)) := by
  intro x
  obtain ⟨C, t, ht, hreachF, hhaltF, hrawOutput, hrawHead,
      hvirtual, hscratch, hinputInv, hinputHead, hworkBoundary,
      houtputParked⟩ :=
    compositionFirstTM_boundary_internal tmF ng hF x
  let boundaryInput := transitionInput C.input
  let boundaryWork : Fin (compositionTapeCount nf ng) → Tape :=
    fun i => transitionTape (C.work i)
  let boundaryOutput := transitionTape C.output
  have htail := compositionTailTM_decides_hoareTime_internal (nf := nf)
    tmG hG (f x) (TF x.length + 1)
  obtain ⟨D, u, hu, hreachTail, hhaltTail, hyesTail, hnoTail⟩ :=
    htail boundaryInput boundaryWork boundaryOutput (by
      refine ⟨hrawOutput, (hworkBoundary _).1, ?_, hvirtual, hscratch,
        houtputParked, hinputInv, hinputHead, ?_⟩
      · dsimp only [boundaryWork]
        omega
      · intro i
        exact hworkBoundary (compositionPrefixIdx nf ng i))
  let first := compositionFirstTM tmF ng
  let tail := compositionTailTM nf ng tmG
  let final := phase2Wrap first tail D
  refine ⟨final, t + 1 + u, ?_, ?_, ?_, ?_, ?_⟩
  · have hlength : (f x).length ≤ TF x.length := hF.output_length_le x
    have hgBound : TG (f x).length ≤ TG (TF x.length) := hmono hlength
    have hu' : u ≤ TF x.length + 1 + 2 * (f x).length + 9 + TG (f x).length := by
      omega
    change t + 1 + u ≤ 4 * TF x.length + 11 + TG (TF x.length)
    omega
  · have hreach := seqTM_reachesIn_of_reachesIn first tail
      hreachF hhaltF hreachTail
    simpa [compositionTM, first, tail, final, boundaryInput, boundaryWork,
      boundaryOutput] using! hreach
  · show (compositionTM tmF tmG).halted final
    simpa [compositionTM, first, tail, final] using!
      (phase2Wrap_halted_iff first tail D).2 hhaltTail
  · intro hx
    simpa [final, phase2Wrap] using! hyesTail hx
  · intro hx
    simpa [final, phase2Wrap] using! hnoTail hx

end TM

end Complexity
