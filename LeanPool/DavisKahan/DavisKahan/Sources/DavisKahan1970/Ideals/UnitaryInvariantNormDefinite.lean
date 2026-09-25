/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.RankOneNormalization

/-!
# Definiteness of the source-defined norm

The finite operator objects used to construct `SymmetricNormingFunction` are
formulated as seminorms because Fan dominance does not need definiteness.
Source normalization removes that apparent extra generality: the first prefix
is exactly the operator norm, so the canonical extension is a genuine norm on
its ideal.  This closes the definition-level correspondence with the norm class
used by Davis and Kahan.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace ENNReal

noncomputable section

universe u v

namespace SymmetricNormingFunction

/-- The one-term source gauge is exactly operator norm. -/
theorem prefixGauge_one_eq_opNorm
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (N : SymmetricNormingFunction) (A : E →L[𝕜] F) :
    N.prefixGauge 1 A = ‖A‖ := by
  unfold prefixGauge approximationPrefix
  have hvec : (fun i : Fin 1 => approximationSingularValue (i : ℕ) A) =
      ‖A‖ • (fun _ : Fin 1 => (1 : ℝ)) := by
    funext i
    fin_cases i
    simp
  rw [hvec, N.finiteGauge_smul, N.finiteGauge_one]
  simp [abs_of_nonneg (norm_nonneg A)]

/-- Every source norm dominates the bound norm on its canonical ideal. -/
theorem opNorm_le_gauge
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (N : SymmetricNormingFunction) {A : E →L[𝕜] F} (hA : N.Mem A) :
    ‖A‖ ≤ N.gauge A := by
  have hprefix : ENNReal.ofReal ‖A‖ ≤ N.extendedGauge A := by
    rw [← N.prefixGauge_one_eq_opNorm A]
    exact le_iSup (fun n : ℕ => ENNReal.ofReal (N.prefixGauge n A)) 1
  have hreal := ENNReal.toReal_mono hA hprefix
  simpa [gauge, ENNReal.toReal_ofReal (norm_nonneg A)] using hreal

/-- The source extension is positive definite. -/
theorem gauge_eq_zero_iff
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (N : SymmetricNormingFunction) {A : E →L[𝕜] F} (hA : N.Mem A) :
    N.gauge A = 0 ↔ A = 0 := by
  constructor
  · intro hzero
    have hop : ‖A‖ = 0 := le_antisymm
      ((N.opNorm_le_gauge hA).trans_eq hzero) (norm_nonneg A)
    exact norm_eq_zero.mp hop
  · rintro rfl
    simp [gauge, N.extendedGauge_zero]

/-- Strict positivity on a nonzero member. -/
theorem gauge_pos
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (N : SymmetricNormingFunction) {A : E →L[𝕜] F}
    (hA : N.Mem A) (hA0 : A ≠ 0) :
    0 < N.gauge A := by
  have hnonneg : 0 ≤ N.gauge A := ENNReal.toReal_nonneg
  exact lt_of_le_of_ne hnonneg (fun h => hA0 ((N.gauge_eq_zero_iff hA).1 h.symm))

end SymmetricNormingFunction

end

end ExactSinTheta
end DavisKahan
end TauCeti
