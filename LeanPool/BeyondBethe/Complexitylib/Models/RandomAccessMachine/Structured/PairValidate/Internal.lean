/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.PairValidate.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Scanner.Internal

/-!
# Structured RAM pair validator — proof internals

The benchmark supplies only its typed scanner specification. State encoding,
execution, correctness, and resource proofs are all in the generic scanner layer.
-/


public section

namespace Complexity

namespace RAM

namespace Structured

namespace PairValidate

theorem program_measured_internal (bits : List Bool) :
    ∃ final cost space,
      Exec program (inputStore bits) final (stepCount bits.length) cost space ∧
      cost ≤ timeBound bits.length ∧ space ≤ spaceBound bits.length ∧
      final lengthReg = Input.bitValue
        (TM.pairValidateAccept (bits.foldl TM.pairValidateStep .next)) := by
  exact Scanner.typed_program_measured_internal typedSpec bits

end PairValidate

end Structured

end RAM

end Complexity
