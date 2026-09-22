/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtApproximationNorm
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm

/-!
# Finite-dimensional Frobenius realization of the paper square norm

On finite-dimensional real or complex Hilbert spaces, the paper square norm
built from approximation singular values is exactly the usual rectangular
Frobenius norm.  This is the missing bridge needed to evaluate the printed
Section 6 counterexample by an ordinary finite column calculation.

## Completeness binders

The paper square energy is defined only for complete spaces, so every statement
below must have `CompleteSpace` available merely to typecheck.  Completeness is
a consequence of finite-dimensionality, but `FiniteDimensional.complete` is
deliberately not an instance in Mathlib, since the scalar field would be an
unknown metavariable during instance resolution.  The binders are therefore
written out.  They cost the caller nothing: `CompleteSpace` is a `Prop` class,
so proof irrelevance identifies whatever instance a call site already carries
with one produced by `letI : CompleteSpace E := FiniteDimensional.complete 𝕜 E`.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace BigOperators ENNReal


noncomputable section

universe u vE vF

/-- In finite dimensions, the paper square energy is the finite sum of the
squares of the ordinary rectangular singular values. -/
theorem approximationNumberEnergy_eq_ofReal_sum_sq_singularValues
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] 
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 F] 
    (A : E →L[𝕜] F) :
    approximationNumberEnergy A =
      ENNReal.ofReal
        (∑ i : Fin (Module.finrank 𝕜 E),
          A.toLinearMap.singularValues (i : ℕ) ^ 2) := by
  -- The accepted equality is phrased on the continuous map built from a linear
  -- map; a continuous map is definitionally rebuilt from its own underlying
  -- linear map, so it transfers to `A` without any further hypothesis.
  have hsv : ∀ n : ℕ,
      approximationSingularValue n A = A.toLinearMap.singularValues n := fun n =>
    approximationSingularValue_eq_singularValues A.toLinearMap n
  unfold approximationNumberEnergy
  rw [tsum_eq_sum (s := Finset.range (Module.finrank 𝕜 E))]
  · rw [← Fin.sum_univ_eq_sum_range,
      ← ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [hsv]
  · intro n hn
    have hfinrank : Module.finrank 𝕜 E ≤ n := by
      simpa only [Finset.mem_range, not_lt] using hn
    rw [hsv, A.toLinearMap.singularValues_of_finrank_le hfinrank]
    simp

/-- In finite dimensions, the basis-free paper norm is exactly the Frobenius norm of the
unified rectangular unitarily invariant seminorm family.  Square operators are the `E = F`
case of this statement; there is no separate square spelling. -/
theorem hilbertSchmidtNorm_eq_frobenius
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    ContinuousLinearMap.hilbertSchmidtNorm A =
      UnitarilyInvariantSeminorm.frobenius A.toLinearMap := by
  rw [hilbertSchmidtNorm_eq_sqrt_approximationNumberEnergy]
  rw [approximationNumberEnergy_eq_ofReal_sum_sq_singularValues,
    ENNReal.toReal_ofReal (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  exact (UnitarilyInvariantSeminorm.frobenius_eq_sqrt_sum_sq_singularValues
    A.toLinearMap).symm

end

end ExactSinTheta
end DavisKahan
end TauCeti
