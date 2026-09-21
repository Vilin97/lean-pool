/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.OperatorNorm
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.TraceClass

/-!
# Ky Fan dominance of rectangular operator ideal families

Domination of every finite Ky Fan gauge implies domination under the family gauge.
This property neither requires nor encodes adjoint symmetry. Source and target
universes remain independent; adjoint-closed families use their base-family projection.

The symmetric-gauge instance is proved in `Family.SymmetricGauge` from sequence
majorization. The concrete instances below follow directly from their gauges.
-/

open scoped ENNReal InnerProductSpace

public section

namespace TauCeti

universe u v w

open _root_.ContinuousLinearMap

/-- **Ky Fan dominance.**  Majorization of every finite Ky Fan gauge forces the ideal gauge
to be dominated too. -/
class IsKyFanDominant {𝕜 : Type u} [RCLike 𝕜] (N : OperatorIdealFamily.{u, v, w} 𝕜) :
    Prop where
  /-- The dominance implication. -/
  gauge_le_of_forall_kyFanGauge_le :
    ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {A B : E →L[𝕜] F},
      (∀ k, A.kyFanGauge k ≤ B.kyFanGauge k) → N.gauge A ≤ N.gauge B

namespace IsKyFanDominant

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Dominance in the two-part form the sine-theta development uses: a majorized operator is
a member whenever the majorizing one is, and its gauge is no larger. -/
theorem mem_carrier_and_gauge_le (N : OperatorIdealFamily.{u, v, w} 𝕜)
    [IsKyFanDominant N] {A B : E →L[𝕜] F}
    (hB : B ∈ N.carrier)
    (hAB : ∀ k, A.kyFanGauge k ≤ B.kyFanGauge k) :
    A ∈ N.carrier ∧ N.gauge A ≤ N.gauge B := by
  have hle := IsKyFanDominant.gauge_le_of_forall_kyFanGauge_le (N := N) hAB
  exact ⟨ne_top_of_le_ne_top hB hle, hle⟩

/-- Equal Ky Fan gauges force equal ideal gauges. -/
theorem gauge_eq_of_forall_kyFanGauge_eq (N : OperatorIdealFamily.{u, v, w} 𝕜)
    [IsKyFanDominant N] {A B : E →L[𝕜] F}
    (h : ∀ k, A.kyFanGauge k = B.kyFanGauge k) :
    N.gauge A = N.gauge B :=
  le_antisymm
    (IsKyFanDominant.gauge_le_of_forall_kyFanGauge_le (N := N) fun k => (h k).le)
    (IsKyFanDominant.gauge_le_of_forall_kyFanGauge_le (N := N) fun k => (h k).ge)

end IsKyFanDominant

/-- The operator norm is the first Ky Fan gauge, so dominance is the `k = 1` instance. -/
instance isKyFanDominant_operatorNormIdealFamily (𝕜 : Type u) [RCLike 𝕜] :
    IsKyFanDominant (operatorNormIdealFamily.{u, v, w} 𝕜) where
  gauge_le_of_forall_kyFanGauge_le {_E _F} _ _ _ _ _ _ {_A _B} h := by
    have h1 := h 1
    rw [ContinuousLinearMap.kyFanGauge_one, ContinuousLinearMap.kyFanGauge_one] at h1
    simpa [operatorNormIdealFamily] using ENNReal.ofReal_le_ofReal h1

/-- A Ky Fan family is dominated by hypothesis at its own index. -/
instance isKyFanDominant_kyFanIdealFamily (𝕜 : Type u) [RCLike 𝕜]
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] (k : ℕ) (hk : 0 < k) :
    IsKyFanDominant (kyFanIdealFamily.{u, v} 𝕜 k hk).toOperatorIdealFamily where
  gauge_le_of_forall_kyFanGauge_le {_E _F} _ _ _ _ _ _ {_A _B} h :=
    ENNReal.ofReal_le_ofReal (h k)

/-- The nuclear norm is the supremum of the Ky Fan gauges, so dominance is monotonicity of
that supremum. -/
instance isKyFanDominant_traceClassIdealFamily (𝕜 : Type u) [RCLike 𝕜]
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] :
    IsKyFanDominant (traceClassIdealFamily.{u, v} 𝕜).toOperatorIdealFamily where
  gauge_le_of_forall_kyFanGauge_le {_E _F} _ _ _ _ _ _ {_A _B} h := by
    rw [gauge_traceClassIdealFamily, gauge_traceClassIdealFamily,
      ContinuousLinearMap.nuclearENorm_eq_iSup_kyFanGauge,
      ContinuousLinearMap.nuclearENorm_eq_iSup_kyFanGauge]
    exact iSup_mono fun k => ENNReal.ofReal_le_ofReal (h k)

end TauCeti
