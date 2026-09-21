/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Defs
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Vec
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Defs
import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal

/-!
# Cobham's characterization of FP — surface layer

Cobham's theorem (1965): the machine-independent function algebra
`Complexity.Cobham` of `Complexitylib.Classes.P.Cobham.Defs` carves out exactly
the polynomial-time computable string functions.

## Main results

- `Cobham.cobham_iff_FPn` — the characterization at every fixed arity
- `CobhamFP_subset_FP` — every function of the algebra is polynomial-time
- `FP_subset_CobhamFP` — every polynomial-time function is in the algebra
- `CobhamFP_eq_FP` — **Cobham's theorem**, the two directions together

## How the two directions are proved

Both halves live in `Complexitylib.Classes.P.Cobham.Internal`.

*Soundness* is the induction `Cobham f → FPn f` over the six constructors, where
`Cobham.FPn` lifts `FP` to argument vectors through the tuple encoding
`Cobham.encodeVec`. Four constructors are bespoke transducers
(`Cobham.cons_mem_FP`, `fstBlock_mem_FP`, `sndBlock_mem_FP`, `reorder_mem_FP`,
`mulLenFn_mem_FP`); the fifth, `boundedRec`, is a loop: recursion on notation is
a fold (`Cobham.recFold_eq_recNotation`), Cobham's side condition makes its width
clamp vacuous (`Cobham.recFoldClamp_eq_recFold`), and `Cobham.iterate_mem_FP`
runs the clamped step once per bit under a polynomial ruler.

*Completeness* simulates a polynomial-time machine inside the algebra. A whole
configuration is one block-aligned bitstring with each tape split at its head, so
a head move is a two-bit shift (`Cobham.cfgCode`); the transition function is the
finite table `Cobham.stepFn`; the run is `Cobham.iterFn` under a clock built from
`smash` (`Cobham.exists_pow_clock`); and the output is read off the output tape
after a rewind (`Cobham.rewindFn`). The assembly is `Cobham.simFn_eq`.
-/


public section

namespace Complexity

namespace Cobham

/-- The canonical fixed-arity tuple encoding is itself a member of Cobham's
algebra. -/
theorem encodeVec_mem {n : ℕ} : Cobham (@encodeVec n) :=
  encodeVec_mem_internal

/-- Multi-arity completeness: every function that is polynomial-time on encoded
argument vectors belongs to Cobham's algebra. -/
theorem FPn_imp_cobham {n : ℕ} {f : (Fin n → List Bool) → List Bool} :
    FPn f → Cobham f :=
  FPn_imp_cobham_internal

/-- **Cobham's theorem at every fixed arity.** A function belongs to Cobham's
algebra exactly when it is polynomial-time on the canonical encoded vectors. -/
theorem cobham_iff_FPn {n : ℕ} {f : (Fin n → List Bool) → List Bool} :
    Cobham f ↔ FPn f :=
  ⟨cobham_imp_FPn, FPn_imp_cobham⟩

end Cobham

/-- Cobham's algebra is sound for polynomial time: every function of the (unary
fragment of the) algebra is computable by a deterministic TM in polynomial time.

The multi-arity soundness induction `Cobham.cobham_imp_FPn`, specialized to
arity one. -/
theorem CobhamFP_subset_FP : CobhamFP ⊆ FP :=
  Cobham.CobhamFP_subset_FP_of_FPn

/-- Cobham's algebra is complete for polynomial time: every polynomial-time
computable function belongs to the algebra.

Proved by simulating the machine inside the algebra (`Cobham.simFn_eq`). -/
theorem FP_subset_CobhamFP : FP ⊆ CobhamFP :=
  Cobham.FP_subset_CobhamFP_internal

/-- **Cobham's theorem** (1965): the machine-independent function algebra of
`Complexitylib.Classes.P.Cobham.Defs` characterizes exactly the polynomial-time
computable string functions. -/
theorem CobhamFP_eq_FP : CobhamFP = FP :=
  Set.Subset.antisymm CobhamFP_subset_FP FP_subset_CobhamFP

end Complexity
