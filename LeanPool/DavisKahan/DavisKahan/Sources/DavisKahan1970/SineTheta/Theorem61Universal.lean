/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Theorem61
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNorm
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.HeterogeneousRepresentative

/-! # Theorem61Universal -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan Theorem 6.1 for every source-defined norm

The compiler-accepted theorem is parameterized by a Ky-Fan-dominant ideal
family.  The source paper instead quantifies over every normalized symmetric
norming function.  This module removes that presentational gap without adding
an independent ideal-membership hypothesis to the norm definition.

The proof first instantiates the accepted theorem with every positive finite
Ky Fan gauge.  The resulting simultaneous prefix inequalities are then passed
to `SymmetricNormingFunction`, whose value is the canonical supremum of the
coherent finite symmetric gauges.  Thus the final quantifier is literally the
one used in Davis--Kahan 1970.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace BigOperators

noncomputable section

universe v

section Complex

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Norm-independent mathematical inputs of Davis--Kahan Theorem 6.1. -/
structure Theorem61Data where
  /-- The norm-independent operator and residual inputs for the complex sine theorem. -/
  data : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G)
  /-- The isometric parametrization of the exact subspace. -/
  exactMap : H →L[ℂ] E
  ambient_selfAdjoint : _root_.IsSelfAdjoint data.A
  trial_selfAdjoint : _root_.IsSelfAdjoint data.A₀
  complement_selfAdjoint : _root_.IsSelfAdjoint data.Λ₁
  exact_decomposition : OrthogonalExactDecomposition exactMap data.F₁
  /-- The positive form gap between the trial and complementary operators. -/
  gap : ℝ
  /-- The positive lower frame bound for the trial map. -/
  frameLowerBound : ℝ
  gap_pos : 0 < gap
  frameLowerBound_pos : 0 < frameLowerBound
  lowerFrame : LowerFrameBound data.X frameLowerBound
  spectral_gap : FormBoundedSylvesterGap data.A₀ data.Λ₁ gap

namespace Theorem61Data

/-- Canonical directed sine block used to state the singular-value condition. -/
def canonicalSinTheta (P : Theorem61Data
    (E := E) (F := F) (G := G) (H := H)) : F →L[ℂ] E :=
  directedSinThetaOperator P.data.X P.exactMap
    P.lowerFrame P.frameLowerBound_pos

/-- Package the norm-independent data for one finite Ky Fan gauge. -/
noncomputable def toKyFanProblem
    (P : Theorem61Data (E := E) (F := F) (G := G) (H := H))
    (k : ℕ) (hk : 0 < k) :
    FormBoundedGeneralSinThetaProblem (E := E) (F := F) (G := G) (H := H)
      (KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) k hk) where
  data := P.data
  exactMap := P.exactMap
  ambient_selfAdjoint := P.ambient_selfAdjoint
  trial_selfAdjoint := P.trial_selfAdjoint
  complement_selfAdjoint := P.complement_selfAdjoint
  exact_decomposition := P.exact_decomposition
  gap := P.gap
  frameLowerBound := P.frameLowerBound
  gap_pos := P.gap_pos
  frameLowerBound_pos := P.frameLowerBound_pos
  lowerFrame := P.lowerFrame
  spectral_gap := P.spectral_gap
  residual_mem := KyFanDominantIdealFamily.kyFan_mem
    (𝕜 := ℂ) k hk P.data.residual

/-- The accepted theorem yields every finite Ky Fan inequality required by the
source Fan-dominance argument. -/
theorem all_kyFan_bound
    (P : Theorem61Data (E := E) (F := F) (G := G) (H := H))
    (S : SinThetaRepresentative P.canonicalSinTheta) :
    ∀ k : ℕ,
      P.gap * P.frameLowerBound * kyFanApproximationGauge k S.operator ≤
        kyFanApproximationGauge k P.data.residual := by
  intro k
  by_cases hk0 : k = 0
  · subst k
    simp only [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge, Finset.range_zero, Finset.sum_empty,
      mul_zero, le_refl]
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    let N := KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) k hk
    have hmain := FormBoundedGeneralSinThetaProblem.result N (P.toKyFanProblem k hk)
    have hsame := S.same_singular_values.kyFanApproximationGauge_eq k
    simpa only [N, KyFanDominantIdealFamily.kyFan_gauge,
      Theorem61Data.toKyFanProblem,
      Theorem61Data.canonicalSinTheta, hsame] using hmain.2

/-- **Davis--Kahan 1970, Theorem 6.1, literal universal-norm form.**

The selected `sin Θ₀` is arbitrary subject only to the complete singular-value
condition stated in the paper, and `N` is an arbitrary normalized coherent
symmetric norming function. -/
theorem result_every_unitarilyInvariantNorm
    (P : Theorem61Data (E := E) (F := F) (G := G) (H := H))
    (S : SinThetaRepresentative P.canonicalSinTheta)
    (N : SymmetricNormingFunction)
    (hR : N.Mem P.data.residual) :
    N.Mem S.operator ∧
      P.gap * P.frameLowerBound * N.gauge S.operator ≤
        N.gauge P.data.residual := by
  have hc : 0 < P.gap * P.frameLowerBound :=
    mul_pos P.gap_pos P.frameLowerBound_pos
  exact N.mul_gauge_le_of_all_mul_kyFan_le hc hR (P.all_kyFan_bound S)

/-- Literal Theorem 6.1 with the representative allowed to act between
arbitrary Hilbert coordinate spaces, as in the source statement. -/
theorem result_every_unitarilyInvariantNorm_across
    {E₀ F₀ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [CompleteSpace F₀]
    (P : Theorem61Data (E := E) (F := F) (G := G) (H := H))
    (S : SinThetaRepresentativeAcross
      (E₀ := E₀) (F₀ := F₀) P.canonicalSinTheta)
    (N : SymmetricNormingFunction)
    (hR : N.Mem P.data.residual) :
    N.Mem S.operator ∧
      P.gap * P.frameLowerBound * N.gauge S.operator ≤
        N.gauge P.data.residual := by
  have hcanonical := P.result_every_unitarilyInvariantNorm
    (SinThetaRepresentative.canonical P.canonicalSinTheta) N hR
  have htransport := S.normingMem_iff_and_gauge_eq N
  refine ⟨htransport.1.mpr hcanonical.1, ?_⟩
  rw [htransport.2]
  exact hcanonical.2

end Theorem61Data

/-- Norm-independent inputs of the original isometric sine theorem. -/
structure IsometricTheoremData where
  /-- The operator and residual inputs for the complex isometric sine theorem. -/
  data : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G)
  /-- The isometric parametrization of the exact subspace. -/
  exactMap : H →L[ℂ] E
  ambient_selfAdjoint : _root_.IsSelfAdjoint data.A
  trial_selfAdjoint : _root_.IsSelfAdjoint data.A₀
  complement_selfAdjoint : _root_.IsSelfAdjoint data.Λ₁
  exact_decomposition : OrthogonalExactDecomposition exactMap data.F₁
  /-- The positive form gap between the trial and complementary operators. -/
  gap : ℝ
  gap_pos : 0 < gap
  trial_isometry : IsometricEmbedding data.X
  spectral_gap : FormBoundedSylvesterGap data.A₀ data.Λ₁ gap

namespace IsometricTheoremData

/-- Forget the isometry hypothesis: an isometric embedding has lower frame bound `1`, so the
isometric record is the general one with `frameLowerBound := 1`. -/
noncomputable def toGeneral
    (P : IsometricTheoremData (E := E) (F := F) (G := G) (H := H)) :
    Theorem61Data (E := E) (F := F) (G := G) (H := H) where
  data := P.data
  exactMap := P.exactMap
  ambient_selfAdjoint := P.ambient_selfAdjoint
  trial_selfAdjoint := P.trial_selfAdjoint
  complement_selfAdjoint := P.complement_selfAdjoint
  exact_decomposition := P.exact_decomposition
  gap := P.gap
  frameLowerBound := 1
  gap_pos := P.gap_pos
  frameLowerBound_pos := zero_lt_one
  lowerFrame := lowerFrameBound_one_of_isometry P.trial_isometry
  spectral_gap := P.spectral_gap

/-- The canonical sine-theta operator of an isometric configuration, read off the general record. -/
def canonicalSinTheta
    (P : IsometricTheoremData (E := E) (F := F) (G := G) (H := H)) :=
  P.toGeneral.canonicalSinTheta

/-- Original isometric sine theorem for every normalized source norm and every
admissible representative coordinate space. -/
theorem result_every_unitarilyInvariantNorm_across
    {E₀ F₀ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [CompleteSpace F₀]
    (P : IsometricTheoremData (E := E) (F := F) (G := G) (H := H))
    (S : SinThetaRepresentativeAcross
      (E₀ := E₀) (F₀ := F₀) P.canonicalSinTheta)
    (N : SymmetricNormingFunction) (hR : N.Mem P.data.residual) :
    N.Mem S.operator ∧
      P.gap * N.gauge S.operator ≤ N.gauge P.data.residual := by
  have h := P.toGeneral.result_every_unitarilyInvariantNorm_across S N hR
  simpa [toGeneral] using h

end IsometricTheoremData

end Complex

section Real

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Real norm-independent mathematical inputs of Theorem 6.1. -/
structure RealTheorem61Data where
  /-- The norm-independent operator and residual inputs for the real sine theorem. -/
  data : UnboundedSinThetaData (𝕜 := ℝ) (E := E) (F := F) (G := G)
  /-- The isometric parametrization of the exact subspace. -/
  exactMap : H →L[ℝ] E
  ambient_selfAdjoint : _root_.IsSelfAdjoint data.A
  trial_selfAdjoint : _root_.IsSelfAdjoint data.A₀
  complement_selfAdjoint : _root_.IsSelfAdjoint data.Λ₁
  exact_decomposition : OrthogonalExactDecomposition exactMap data.F₁
  /-- The positive form gap between the trial and complementary operators. -/
  gap : ℝ
  /-- The positive lower frame bound for the trial map. -/
  frameLowerBound : ℝ
  gap_pos : 0 < gap
  frameLowerBound_pos : 0 < frameLowerBound
  lowerFrame : LowerFrameBound data.X frameLowerBound
  spectral_gap : FormBoundedSylvesterGap data.A₀ data.Λ₁ gap

namespace RealTheorem61Data

/-- Real canonical directed sine block. -/
def canonicalSinTheta (P : RealTheorem61Data
    (E := E) (F := F) (G := G) (H := H)) : F →L[ℝ] E :=
  directedSinThetaOperatorReal P.data.X P.exactMap
    P.lowerFrame P.frameLowerBound_pos

/-- Real data specialized to one finite Ky Fan gauge. -/
noncomputable def toKyFanProblem
    (P : RealTheorem61Data (E := E) (F := F) (G := G) (H := H))
    (k : ℕ) (hk : 0 < k) :
    RealGeneralSinThetaProblem (E := E) (F := F) (G := G) (H := H)
      (KyFanDominantIdealFamily.kyFan (𝕜 := ℝ) k hk) where
  data := P.data
  exactMap := P.exactMap
  ambient_selfAdjoint := P.ambient_selfAdjoint
  trial_selfAdjoint := P.trial_selfAdjoint
  complement_selfAdjoint := P.complement_selfAdjoint
  exact_decomposition := P.exact_decomposition
  gap := P.gap
  frameLowerBound := P.frameLowerBound
  gap_pos := P.gap_pos
  frameLowerBound_pos := P.frameLowerBound_pos
  lowerFrame := P.lowerFrame
  spectral_gap := P.spectral_gap
  residual_mem := KyFanDominantIdealFamily.kyFan_mem
    (𝕜 := ℝ) k hk P.data.residual

/-- Every real finite Ky Fan inequality. -/
theorem all_kyFan_bound
    (P : RealTheorem61Data (E := E) (F := F) (G := G) (H := H))
    (S : SinThetaRepresentative P.canonicalSinTheta) :
    ∀ k : ℕ,
      P.gap * P.frameLowerBound * kyFanApproximationGauge k S.operator ≤
        kyFanApproximationGauge k P.data.residual := by
  intro k
  by_cases hk0 : k = 0
  · subst k
    simp only [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge, Finset.range_zero, Finset.sum_empty,
      mul_zero, le_refl]
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    let N := KyFanDominantIdealFamily.kyFan (𝕜 := ℝ) k hk
    have hmain := RealGeneralSinThetaProblem.result N (P.toKyFanProblem k hk)
    have hsame := S.same_singular_values.kyFanApproximationGauge_eq k
    simpa only [N, KyFanDominantIdealFamily.kyFan_gauge,
      RealTheorem61Data.toKyFanProblem,
      RealTheorem61Data.canonicalSinTheta, hsame] using hmain.2

/-- Literal real Theorem 6.1 for every source-defined norm. -/
theorem result_every_unitarilyInvariantNorm
    (P : RealTheorem61Data (E := E) (F := F) (G := G) (H := H))
    (S : SinThetaRepresentative P.canonicalSinTheta)
    (N : SymmetricNormingFunction)
    (hR : N.Mem P.data.residual) :
    N.Mem S.operator ∧
      P.gap * P.frameLowerBound * N.gauge S.operator ≤
        N.gauge P.data.residual := by
  have hc : 0 < P.gap * P.frameLowerBound :=
    mul_pos P.gap_pos P.frameLowerBound_pos
  exact N.mul_gauge_le_of_all_mul_kyFan_le hc hR (P.all_kyFan_bound S)

/-- Real literal Theorem 6.1 with arbitrary representative coordinate
spaces. -/
theorem result_every_unitarilyInvariantNorm_across
    {E₀ F₀ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace ℝ F₀] [CompleteSpace F₀]
    (P : RealTheorem61Data (E := E) (F := F) (G := G) (H := H))
    (S : SinThetaRepresentativeAcross
      (E₀ := E₀) (F₀ := F₀) P.canonicalSinTheta)
    (N : SymmetricNormingFunction)
    (hR : N.Mem P.data.residual) :
    N.Mem S.operator ∧
      P.gap * P.frameLowerBound * N.gauge S.operator ≤
        N.gauge P.data.residual := by
  have hcanonical := P.result_every_unitarilyInvariantNorm
    (SinThetaRepresentative.canonical P.canonicalSinTheta) N hR
  have htransport := S.normingMem_iff_and_gauge_eq N
  refine ⟨htransport.1.mpr hcanonical.1, ?_⟩
  rw [htransport.2]
  exact hcanonical.2

end RealTheorem61Data

/-- Real norm-independent inputs of the original isometric sine theorem. -/
structure RealIsometricTheoremData where
  /-- The operator and residual inputs for the real isometric sine theorem. -/
  data : UnboundedSinThetaData (𝕜 := ℝ) (E := E) (F := F) (G := G)
  /-- The isometric parametrization of the exact subspace. -/
  exactMap : H →L[ℝ] E
  ambient_selfAdjoint : _root_.IsSelfAdjoint data.A
  trial_selfAdjoint : _root_.IsSelfAdjoint data.A₀
  complement_selfAdjoint : _root_.IsSelfAdjoint data.Λ₁
  exact_decomposition : OrthogonalExactDecomposition exactMap data.F₁
  /-- The positive form gap between the trial and complementary operators. -/
  gap : ℝ
  gap_pos : 0 < gap
  trial_isometry : IsometricEmbedding data.X
  spectral_gap : FormBoundedSylvesterGap data.A₀ data.Λ₁ gap

namespace RealIsometricTheoremData

/-- Forget the isometry hypothesis, real-scalar case. -/
noncomputable def toGeneral
    (P : RealIsometricTheoremData
      (E := E) (F := F) (G := G) (H := H)) :
    RealTheorem61Data (E := E) (F := F) (G := G) (H := H) where
  data := P.data
  exactMap := P.exactMap
  ambient_selfAdjoint := P.ambient_selfAdjoint
  trial_selfAdjoint := P.trial_selfAdjoint
  complement_selfAdjoint := P.complement_selfAdjoint
  exact_decomposition := P.exact_decomposition
  gap := P.gap
  frameLowerBound := 1
  gap_pos := P.gap_pos
  frameLowerBound_pos := zero_lt_one
  lowerFrame := lowerFrameBound_one_of_isometry P.trial_isometry
  spectral_gap := P.spectral_gap

/-- The canonical sine-theta operator of a real isometric configuration. -/
def canonicalSinTheta
    (P : RealIsometricTheoremData
      (E := E) (F := F) (G := G) (H := H)) :=
  P.toGeneral.canonicalSinTheta

/-- Real original sine theorem for every normalized source norm and every
admissible representative coordinate space. -/
theorem result_every_unitarilyInvariantNorm_across
    {E₀ F₀ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace ℝ F₀] [CompleteSpace F₀]
    (P : RealIsometricTheoremData
      (E := E) (F := F) (G := G) (H := H))
    (S : SinThetaRepresentativeAcross
      (E₀ := E₀) (F₀ := F₀) P.canonicalSinTheta)
    (N : SymmetricNormingFunction) (hR : N.Mem P.data.residual) :
    N.Mem S.operator ∧
      P.gap * N.gauge S.operator ≤ N.gauge P.data.residual := by
  have h := P.toGeneral.result_every_unitarilyInvariantNorm_across S N hR
  simpa [toGeneral] using h

end RealIsometricTheoremData

end Real

end

end ExactSinTheta
end DavisKahan
end TauCeti
