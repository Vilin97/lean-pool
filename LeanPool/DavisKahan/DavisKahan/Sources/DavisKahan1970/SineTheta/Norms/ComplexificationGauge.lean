/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNorm
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ComplexificationApproximation

/-! # Complexification Gauge -/

open TauCeti.DavisKahan.Sylvester

/-!
# Source unitarily-invariant norms are preserved by real complexification

Standing assumption 1 of Davis--Kahan 1970 is that the Hilbert space is "real or
complex".  Almost all of the analysis in this repository is carried out over `ℂ`,
so the real half of that assumption has to be reached by complexification.  This
module supplies the norm half of that transfer.

The point is that `SymmetricNormingFunction` is already scalar-agnostic *at the
operator level*: although its finite model `finiteNorm` is a family of unitarily
invariant seminorms on complex Euclidean spaces, an operator only ever enters
through `approximationPrefix`, i.e. through its approximation singular values.
Since `approximationSingularValue_complexify` says those are preserved exactly,
every layer built on top of them is preserved too, and none of the four proofs
below has any content beyond that one identity:

* `approximationPrefix_complexify` -- the singular-value prefix vectors agree;
* `prefixGauge_complexify` -- hence so does each finite gauge;
* `extendedGauge_complexify` -- hence so does their `ENNReal` supremum;
* `mem_complexify_iff`, `gauge_complexify` -- hence so do ideal membership and
  the real-valued norm.

`gauge_complexify` is the one that matters downstream: it lets a real
Davis--Kahan statement whose conclusion is `δ * N.gauge X ≤ N.gauge C` be read
off from the complex statement about `complexify X` and `complexify C`, for
*every* source unitarily-invariant norm at once, with no per-norm argument.

Everything here is stated for `E` and `F` in a single universe because
`approximationPrefix` and `prefixGauge` are.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

namespace SymmetricNormingFunction

open scoped ENNReal
open TauCeti.RealComplexification

universe v

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The approximation singular-value prefix of a real operator is unchanged by
complexification.  This is `approximationSingularValue_complexify` read
coordinatewise, and it is the only mathematical input to this file. -/
theorem approximationPrefix_complexify (n : ℕ) (T : E →L[ℝ] F) :
    approximationPrefix n (RealComplexification.complexify T) =
      approximationPrefix n T := by
  funext i
  exact ComplexificationApproximation.approximationSingularValue_complexify T _

/-- Each finite prefix gauge of a source norm is unchanged by complexification. -/
theorem prefixGauge_complexify (N : SymmetricNormingFunction) (n : ℕ)
    (T : E →L[ℝ] F) :
    N.prefixGauge n (RealComplexification.complexify T) = N.prefixGauge n T := by
  unfold prefixGauge
  rw [approximationPrefix_complexify]

/-- The extended (`ENNReal`-valued) source gauge is unchanged by
complexification. -/
theorem extendedGauge_complexify (N : SymmetricNormingFunction)
    (T : E →L[ℝ] F) :
    N.extendedGauge (RealComplexification.complexify T) = N.extendedGauge T := by
  unfold extendedGauge
  exact iSup_congr fun n => by rw [prefixGauge_complexify]

/-- Membership in the ideal of a source norm is unchanged by complexification. -/
theorem mem_complexify_iff (N : SymmetricNormingFunction) (T : E →L[ℝ] F) :
    N.Mem (RealComplexification.complexify T) ↔ N.Mem T := by
  unfold Mem
  rw [extendedGauge_complexify]

/-- **Every source unitarily-invariant norm is preserved by real
complexification.**  This is the transport lemma the real Davis--Kahan wrappers
consume: a complex conclusion `δ * N.gauge (complexify X) ≤ N.gauge (complexify C)`
is literally the real conclusion `δ * N.gauge X ≤ N.gauge C`. -/
theorem gauge_complexify (N : SymmetricNormingFunction) (T : E →L[ℝ] F) :
    N.gauge (RealComplexification.complexify T) = N.gauge T := by
  unfold gauge
  rw [extendedGauge_complexify]

end SymmetricNormingFunction

end ExactSinTheta
end DavisKahan
end TauCeti
