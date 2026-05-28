/-
Copyright (c) 2026 Luka Opravš. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luka Opravš
-/
import LeanPool.PolyaEnumerationTheorem.Concrete

/-!
## Stirling numbers of the first kind

The Stirling numbers of the first kind, defined here as the number of permutations of a finite
set with a given number of cycles.

For additional information, refer to
<https://en.wikipedia.org/wiki/Stirling_numbers_of_the_first_kind>.
-/

namespace LeanPool.PolyaEnumerationTheorem

namespace StirlingFirstKindSum

open CyclesOfGroupElements

/-- The Stirling number of the first kind `stirlingFirstKind n i` represents the number of
    permutations of `Fin n` with exactly `i` cycles. -/
abbrev stirlingFirstKind (n i : ℕ) : ℕ :=
  numGroupOfNumCycles (Fin n) (Equiv.Perm (Fin n)) i

end StirlingFirstKindSum

end LeanPool.PolyaEnumerationTheorem
