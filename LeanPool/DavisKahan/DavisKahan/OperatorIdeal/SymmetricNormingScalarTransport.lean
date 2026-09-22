/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNorm
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.ScalarTransport

/-!
# Symmetric norming functions under `RCLike` scalar transport

`ScalarTransport` renames the scalar field without changing vectors, norms,
ranks, or approximation numbers.  A `SymmetricNormingFunction` depends only on
the approximation singular-value sequence, so its prefix gauges, extended
gauge, ideal membership, and ordinary gauge are all invariant as well.

These lemmas are the norm-side adapter for scalar-generic source theorems proved
by dispatching an arbitrary `RCLike` field to its real or complex model.  They
are intentionally independent of Davis--Kahan tangent geometry.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta
namespace SymmetricNormingFunction

open TauCeti.ScalarTransport

universe u w v

variable {𝕜 : Type u} {𝕂 : Type w} [RCLike 𝕜] [RCLike 𝕂]
variable {e : RCLikeIso 𝕜 𝕂}
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Approximation singular-value prefixes are unchanged by scalar transport. -/
theorem approximationPrefix_clm (n : ℕ) (T : E →L[𝕜] F) :
    approximationPrefix n (clm (e := e) T) = approximationPrefix n T := by
  funext i
  exact ScalarTransport.approximationNumber_clm (e := e) T _

omit [CompleteSpace E] [CompleteSpace F] in
/-- Every finite source gauge is unchanged by scalar transport. -/
theorem prefixGauge_clm (N : SymmetricNormingFunction) (n : ℕ) (T : E →L[𝕜] F) :
    N.prefixGauge n (clm (e := e) T) = N.prefixGauge n T := by
  unfold prefixGauge
  rw [approximationPrefix_clm]

/-- The extended source gauge is unchanged by scalar transport. -/
theorem extendedGauge_clm (N : SymmetricNormingFunction) (T : E →L[𝕜] F) :
    N.extendedGauge (clm (e := e) T) = N.extendedGauge T := by
  unfold extendedGauge
  exact iSup_congr fun n => by rw [prefixGauge_clm]

/-- Membership in the source norm ideal is unchanged by scalar transport. -/
theorem mem_clm_iff (N : SymmetricNormingFunction) (T : E →L[𝕜] F) :
    N.Mem (clm (e := e) T) ↔ N.Mem T := by
  unfold Mem
  rw [extendedGauge_clm]

/-- Every source unitarily invariant gauge is unchanged by scalar transport. -/
theorem gauge_clm (N : SymmetricNormingFunction) (T : E →L[𝕜] F) :
    N.gauge (clm (e := e) T) = N.gauge T := by
  unfold gauge
  rw [extendedGauge_clm]

end SymmetricNormingFunction
end ExactSinTheta
end DavisKahan
end TauCeti
