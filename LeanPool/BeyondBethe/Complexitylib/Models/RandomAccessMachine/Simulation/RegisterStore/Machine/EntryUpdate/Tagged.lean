/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.TaggedProof

/-!
# Positive-tag sparse updates
-/


@[expose] public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

/-- Successor tagging followed by sparse update implements one dense-overlay
write and preserves the complete encoded-source frame. -/
theorem taggedEntryUpdateTM_hoareTime_frame {n : ℕ}
    (tapes : EntryUpdateTapes n) (overlay : Store) (address value : ℕ)
    (emittedBits : List Bool) (initialWork : Fin n → Tape)
    (inp₀ out₀ : Tape) (hcanonical : Canonical overlay)
    (hready : EntryScanReady tapes.entry (overlay.flatMap Entry.encode)
      address.bits initialWork initialWork)
    (hreplacement : (initialWork tapes.replacement).HasBinaryNat value)
    (hremaining :
      (initialWork tapes.remaining).HasBinaryNat overlay.length)
    (hfound : (initialWork tapes.found).HasBinaryNat 0)
    (hresultCount :
      (initialWork tapes.resultCount).HasBinaryNat overlay.length)
    (hinput : TM.Parked inp₀)
    (houtput : out₀.HasBinaryPrefix emittedBits) :
    (taggedEntryUpdateTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        TaggedEntryUpdateResult tapes overlay address value initialWork work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (DenseOverlay.write overlay address value).flatMap Entry.encode))
      (taggedEntryUpdateTime tapes overlay address value) :=
  taggedEntryUpdateTM_hoareTime_frame_internal tapes overlay address value
    emittedBits initialWork inp₀ out₀ hcanonical hready hreplacement
    hremaining hfound hresultCount hinput houtput

end Machine
end RegisterStore
end RAM
end Complexity
