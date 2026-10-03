/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.FormBoundedGap
public import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ComplexificationApproximation

/-!
# Real unbounded Sylvester theorem by complexification

The complex theorem is applied separately to every positive finite Ky Fan
gauge.  Closed-operator complexification preserves self-adjointness, all three
gap configurations, and the domain-aware equation.  Exact invariance of the
finite Ky Fan gauges then returns the sharp majorization to the real Hilbert
spaces, where the supplied real ideal family's Fan-dominance field produces
membership and the arbitrary-gauge estimate.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan
namespace Sylvester

open scoped InnerProductSpace
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.RealComplexification

noncomputable section

universe v

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

open PartialMapComplexification
open ComplexificationApproximation

/-- Finite Ky Fan majorization for a real domain-aware Sylvester equation,
obtained by applying the complex theorem to the coordinatewise
complexification. -/
theorem real_unbounded_sylvester_kyFan
    {A : E →ₗ.[ℝ] E}
    {B : F →ₗ.[ℝ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X C : F →L[ℝ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A B δ)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (k : ℕ) :
    δ * kyFanApproximationGauge k X ≤
      kyFanApproximationGauge k C := by
  by_cases hk : k = 0
  · subst k
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    let K := KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) k hkpos
    have hcomplex := davisKahan1970_sylvester_complex K
      (isSelfAdjoint_complexify hA)
      (isSelfAdjoint_complexify hB)
      hδ (unboundedSylvesterGap_complexify hgap)
      (closedSylvesterEquation_complexify hEq)
      (KyFanDominantIdealFamily.kyFan_mem k hkpos
        (RealComplexification.complexify C))
    have hbound := hcomplex.2
    simp only [K] at hbound
    rw [KyFanDominantIdealFamily.kyFan_gauge (𝕜 := ℂ) k hkpos
      (RealComplexification.complexify X),
      KyFanDominantIdealFamily.kyFan_gauge (𝕜 := ℂ) k hkpos
        (RealComplexification.complexify C)] at hbound
    simpa only [kyFanApproximationGauge_complexify] using hbound

/-- Real specialization of the full source-facing unbounded Sylvester theorem.
It supports interval/exterior separation and both ordered half-line
orientations, with the same sharp constant and an arbitrary real unitarily
invariant ideal family. -/
theorem davisKahan1970_sylvester_real
    (N : FanDominantIdealFamily (𝕜 := ℝ))
    {A : E →ₗ.[ℝ] E}
    {B : F →ₗ.[ℝ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X C : F →L[ℝ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A B δ)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (hC : N.Mem C) :
    N.Mem X ∧
      δ * N.gauge X ≤
        N.gauge C := by
  apply mem_and_scaled_gauge_le_of_all_scaled_kyFan_le N hδ hC
  intro k
  exact real_unbounded_sylvester_kyFan hA hB hδ hgap hEq k

end

end Sylvester
end DavisKahan
end TauCeti
