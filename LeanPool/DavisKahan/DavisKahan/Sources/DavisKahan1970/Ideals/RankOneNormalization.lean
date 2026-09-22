/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNormLaws
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtFiniteRank

/-!
# Rank-one normalization for the source norm class

The sharpness argument in Davis--Kahan uses only one consequence of source
normalization: every norm-one rank-one operator has norm one.  This module
derives that statement from the coherent finite gauges rather than adding it
to the definition.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace ENNReal

noncomputable section

universe u v

namespace SymmetricNormingFunction

/-- The vector `(1,0,...,0)` in dimension `n+1`. -/
def firstCoordinateVector (n : ℕ) : Fin (n + 1) → ℝ :=
  fun i => if (i : ℕ) = 0 then 1 else 0

/-- The first coordinate vector of the zero map is zero. -/
@[simp]
theorem firstCoordinateVector_zero :
    firstCoordinateVector 0 = (fun _ : Fin 1 => 1) := by
  funext i
  fin_cases i
  simp [firstCoordinateVector]

/-- Coherent zero padding fixes the gauge of `(1,0,...,0)` in every positive
dimension. -/
theorem finiteGauge_firstCoordinateVector
    (N : SymmetricNormingFunction) (n : ℕ) :
    N.finiteGauge (n + 1) (firstCoordinateVector n) = 1 := by
  induction n with
  | zero => simpa [firstCoordinateVector] using N.finiteGauge_one
  | succ n ih =>
      have hpad : firstCoordinateVector (n + 1) =
          zeroPad (firstCoordinateVector n) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [firstCoordinateVector, zeroPad]
        · simp [firstCoordinateVector, zeroPad]
      rw [hpad, N.finiteGauge_zeroPad, ih]

/-- Complete approximation singular-value sequence of a norm-one rank-at-most-
one operator. -/
theorem approximationSingularValue_rankOne
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    {V : E →L[𝕜] F} (hVnorm : ‖V‖ = 1)
    (hVrank : V.rank ≤ (1 : Cardinal)) (n : ℕ) :
    approximationSingularValue n V = if n = 0 then 1 else 0 := by
  rcases n with _ | n
  · simp [hVnorm]
  · rw [ite_eq_right (Nat.succ_ne_zero n)]
    exact approximationSingularValue_eq_zero_of_rank_le_nat hVrank
      (Nat.succ_le_succ (Nat.zero_le n))

/-- Every positive prefix of a normalized rank-one operator has source gauge
one. -/
theorem prefixGauge_rankOne
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (N : SymmetricNormingFunction) {V : E →L[𝕜] F}
    (hVnorm : ‖V‖ = 1) (hVrank : V.rank ≤ (1 : Cardinal)) (n : ℕ) :
    N.prefixGauge (n + 1) V = 1 := by
  unfold prefixGauge approximationPrefix
  have hv : (fun i : Fin (n + 1) => approximationSingularValue (i : ℕ) V) =
      firstCoordinateVector n := by
    funext i
    rw [approximationSingularValue_rankOne hVnorm hVrank]
    simp [firstCoordinateVector]
  rw [hv, N.finiteGauge_firstCoordinateVector]

/-- Source normalization extends exactly to every norm-one rank-one bounded
operator. -/
theorem extendedGauge_rankOne
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (N : SymmetricNormingFunction) {V : E →L[𝕜] F}
    (hVnorm : ‖V‖ = 1) (hVrank : V.rank ≤ (1 : Cardinal)) :
    N.extendedGauge V = 1 := by
  apply le_antisymm
  · apply iSup_le
    intro n
    rcases n with _ | n
    · have hx : approximationPrefix (𝕜 := 𝕜) (E := E) (F := F) 0 V = 0 :=
        Subsingleton.elim _ _
      have hz : N.prefixGauge 0 V = 0 := by
        rw [prefixGauge, hx]
        simpa using N.finiteGauge_smul (n := 0) 0 (0 : Fin 0 → ℝ)
      rw [hz]
      simp
    · rw [N.prefixGauge_rankOne hVnorm hVrank n]
      simp
  · rw [extendedGauge]
    refine le_trans ?_
      (le_iSup (fun n : ℕ => ENNReal.ofReal (N.prefixGauge n V)) 1)
    rw [N.prefixGauge_rankOne hVnorm hVrank 0]
    simp

/-- A norm-one rank-one operator belongs to every source ideal. -/
theorem mem_rankOne
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (N : SymmetricNormingFunction) {V : E →L[𝕜] F}
    (hVnorm : ‖V‖ = 1) (hVrank : V.rank ≤ (1 : Cardinal)) :
    N.Mem V := by
  unfold Mem
  rw [N.extendedGauge_rankOne hVnorm hVrank]
  simp

/-- Every source norm assigns value one to a norm-one rank-one operator. -/
theorem gauge_rankOne
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (N : SymmetricNormingFunction) {V : E →L[𝕜] F}
    (hVnorm : ‖V‖ = 1) (hVrank : V.rank ≤ (1 : Cardinal)) :
    N.gauge V = 1 := by
  unfold gauge
  rw [N.extendedGauge_rankOne hVnorm hVrank]
  simp

end SymmetricNormingFunction

end

end ExactSinTheta
end DavisKahan
end TauCeti
