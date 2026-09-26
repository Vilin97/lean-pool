/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.NormalizedUnitaryInvariantNorm
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.RankOneNormalization

/-!
# The source norm class is inhabited

`NormalizedUnitaryInvariantNorm` is the Lean type for Davis--Kahan's Section 1
norm class, and every source-exact façade quantifies over it.  A universally
quantified statement over an *empty* type is vacuous, so the façades mean nothing
until the class is shown to have members.

Until 2026-09-05 the repository never constructed one.  This module does: the
`k`-th Ky Fan norm is a member for every `k ≥ 1`, and those are the norms Davis
and Kahan's own Fan-dominance argument runs over.

**What was and was not missing.**  The layer beneath,
`KyFanDominantIdealFamily`, was already inhabited by
`KyFanDominantIdealFamily.kyFan`, so this module builds on that rather than
repeating it.  What had no witness was the *normalized* class: the single extra
field `gauge_rankOne_eq_one`, which is the source's `‖u v*‖ = ‖u‖ ‖v‖` after
scaling both vectors to norm one.  It is discharged by
`approximationSingularValue_rankOne`, which says a norm-one rank-one operator has
singular values `1, 0, 0, …`, so the Ky Fan sum of the first `k ≥ 1` of them is
`1`.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]

/-- **The `k`-th Ky Fan norm as a member of the source norm class.** -/
noncomputable def kyFanNormalizedUnitaryInvariantNorm
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] (k : ℕ) (hk : 0 < k) :
    NormalizedUnitaryInvariantNorm.{u, v} 𝕜 where
  toFanDominantIdealFamily := (KyFanDominantIdealFamily.kyFan k hk).toFanDominantIdealFamily
  gauge_rankOne_eq_one := by
    intro E F _ _ _ _ _ _ V hVnorm hVrank
    change ((kyFanSymmetricIdealFamily (𝕜 := 𝕜) k hk).gauge V).toReal = 1
    rw [gauge_kyFanSymmetricIdealFamily, ENNReal.toReal_ofReal
      (kyFanApproximationGauge_nonneg k V)]
    have hsum : kyFanApproximationGauge k V
        = ∑ n ∈ Finset.range k, approximationSingularValue n V := rfl
    rw [hsum]
    have hval : ∀ n ∈ Finset.range k,
        approximationSingularValue n V = if n = 0 then 1 else 0 := fun n _ =>
      SymmetricNormingFunction.approximationSingularValue_rankOne hVnorm hVrank n
    rw [Finset.sum_congr rfl hval, Finset.sum_ite_eq' (Finset.range k) 0 (fun _ => (1 : ℝ))]
    simp [hk]

/-- The gauge of the Ky Fan member is the Ky Fan gauge, definitionally. -/
@[simp]
theorem gauge_kyFanNormalizedUnitaryInvariantNorm
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] (k : ℕ) (hk : 0 < k)
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    (kyFanNormalizedUnitaryInvariantNorm (𝕜 := 𝕜) k hk).gauge A
      = kyFanApproximationGauge k A :=
  ENNReal.toReal_ofReal (kyFanApproximationGauge_nonneg k A)

/-- Every bounded operator lies in the Ky Fan member's ideal. -/
theorem mem_kyFanNormalizedUnitaryInvariantNorm
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] (k : ℕ) (hk : 0 < k)
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    (kyFanNormalizedUnitaryInvariantNorm (𝕜 := 𝕜) k hk).Mem A :=
  gauge_kyFanSymmetricIdealFamily_ne_top k hk A

/-- **The source norm class is inhabited over `ℂ`.**  So every source-exact
façade quantifying over `NormalizedUnitaryInvariantNorm ℂ` says something. -/
theorem nonempty_normalizedUnitaryInvariantNorm_complex :
    Nonempty (NormalizedUnitaryInvariantNorm.{0, v} ℂ) :=
  ⟨kyFanNormalizedUnitaryInvariantNorm (𝕜 := ℂ) 1 one_pos⟩

/-- **The source norm class is inhabited over `ℝ`.** -/
theorem nonempty_normalizedUnitaryInvariantNorm_real :
    Nonempty (NormalizedUnitaryInvariantNorm.{0, v} ℝ) :=
  ⟨kyFanNormalizedUnitaryInvariantNorm (𝕜 := ℝ) 1 one_pos⟩

end

end ExactSinTheta
end DavisKahan
end TauCeti
