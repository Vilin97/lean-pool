/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Basic
/-!
# Compiled local stage of the profinite-unit decomposition
-/

@[expose] public section

open scoped Topology

noncomputable
section

namespace KummerTheory.ProfiniteUnitDecomposition.Internal

open LocalFieldTheory.Padic

/-- The product of the local finite/free decompositions, compiled separately
from the global coordinate-reassembly stages. -/
noncomputable def localDecomposition :
    ((p : Nat.Primes) →
      padicUnitFiniteFactor p.1 × Multiplicative ℤ_[p.1]) ≃ₜ*
    ((p : Nat.Primes) → ℤ_[p.1]ˣ) :=
  continuousMulEquivPiCongr fun p =>
    padicUnitDecomposition p.1

end KummerTheory.ProfiniteUnitDecomposition.Internal
