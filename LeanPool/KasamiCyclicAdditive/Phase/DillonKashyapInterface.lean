/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import LeanPool.KasamiCyclicAdditive.Statement.Definitions
import LeanPool.KasamiCyclicAdditive.Phase.CharacterSums

/-!
# The Dillon--Kashyap phase formula, as a hypothesis

The one statement this development takes from the literature is fixed here as
a `Prop`-valued *definition*, never as an `axiom`.  Nothing is assumed
globally: every theorem that uses it carries it as an explicit hypothesis, and
`MCM/PhaseFormula.lean` then discharges it internally, so `#print axioms` on the final
theorem lists only `propext`, `Classical.choice` and `Quot.sound`.

Provenance: Theorems 1--2 of J. F. Dillon and N. Kashyap, *Jacobi-like sums and
difference sets with Singer parameters*, Australas. J. Combin. 55 (2013),
49--63.  Their Theorem 1 gives the Fourier coefficient
`G(χ) G(χ^(2^k+1)) / G(χ³)` and their Theorem 2 identifies the corresponding
difference set as the complement of this same `Δ`; the sign convention here is
therefore opposite to theirs.
-/

open Finset

namespace KasamiCyclicAdditive

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- For every multiplicative character `χ`,
`F̂(χ) = G(χ) G(χ^(2^k+1)) / G(χ³)`, where `F = +1` on `Δ*` and `-1` off it.

The substantive imported theorem: it supplies the *phases*, not merely the
magnitudes, of the Kasami Fourier spectrum.  Dillon--Kashyap Theorems 1--2, in
the sign convention used here. -/
def DillonKashyapPhaseFormula (k : ℕ) (ψ : AddChar K ℂ) : Prop :=
  ∀ χ : MulChar K ℂ,
    (∑ x : Kˣ, (if (x : K) ∈ derivativeImage k K then (1 : ℂ) else -1) * χ (x : K))
      = gaussSum χ ψ * gaussSum (χ ^ (2 ^ k + 1)) ψ / gaussSum (χ ^ 3) ψ

omit [DecidableEq K] in
/-- **Non-degeneracy of the phase formula.**  In Lean `x / 0 = 0`, so if the
denominator `G(χ³)` could vanish the right-hand side of
`DillonKashyapPhaseFormula` would silently become the junk value `0` and the
whole property could be satisfiable only by accident.  For a primitive additive
character no Gauss sum vanishes, so the quotient is a genuine division. -/
lemma gaussSum_cube_ne_zero {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    (χ : MulChar K ℂ) : gaussSum (χ ^ 3) ψ ≠ 0 :=
  gaussSum_ne_zero_of_primitive hψ _

end KasamiCyclicAdditive
