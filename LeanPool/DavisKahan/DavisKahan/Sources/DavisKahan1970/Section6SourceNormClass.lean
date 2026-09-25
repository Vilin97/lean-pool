/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SymmetricNormingFanDominance
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Proposition61
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Theorem61

/-!
# Proposition 6.1 and Theorem 6.1 over the literal source norm class

Both are printed for every unitary-invariant norm.  The compiled endpoints are
stated over `SymmetricNormingFunction`, one model of that class; these are the
printed statements, over `NormalizedUnitaryInvariantNorm`.

Each is a single application of the Fan-dominance bridge with the printed
constant on the left -- `δ` for Proposition 6.1, `δ ε` for Theorem 6.1 -- so no
mathematics is added.  What changes is the quantifier at the public boundary.

The broader `FormBoundedSylvesterGap` hypothesis is kept rather than specialized:
it is the gap the compiled theorems take, it subsumes the printed interval
geometry, and narrowing it here would make the façade state *less* than what is
proved without bringing it closer to the paper.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan1970

open DavisKahan
open DavisKahan.ExactSinTheta

noncomputable section

universe u v

/-- **Davis--Kahan 1970, Proposition 6.1 over the literal source norm class, over
`ℂ`.**

The symmetric two-sided gap hypothesis and the printed conclusion
`delta ‖sin Theta‖ ≤ ‖B − A‖`, for every normalized unitarily invariant norm. -/
theorem proposition6_1_sourceExact_complex
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    {A B : E →L[ℂ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgapUV : DavisKahan.Sylvester.FormBoundedSylvesterGap
      (DavisKahanExt.PartialMap.boundedReducingBlock A U hU)
      (DavisKahanExt.PartialMap.boundedReducingBlockCompl B V hV) δ)
    (hgapVU : DavisKahan.Sylvester.FormBoundedSylvesterGap
      (DavisKahanExt.PartialMap.boundedReducingBlock B V hV)
      (DavisKahanExt.PartialMap.boundedReducingBlockCompl A U hU) δ)
    (hMem : N.Mem (B - A)) :
    N.Mem (DavisKahan.Angle.sinAngleOperatorC U V) ∧
      δ * N.gauge (DavisKahan.Angle.sinAngleOperatorC U V) ≤ N.gauge (B - A) :=
  normalizedUnitaryInvariant_of_symmetricNorming
    (X := DavisKahan.Angle.sinAngleOperatorC U V) (Y := B - A)
    N hδ hMem fun M hM =>
      proposition6_1_complex M hA hB hU hV hδ hgapUV hgapVU hM

/-- **Davis--Kahan 1970, Proposition 6.1 over the literal source norm class, over
`ℝ`.**

The real conclusion is on the projector difference `P_V − P_U`, which is the
repository's real directed sine object. -/
theorem proposition6_1_sourceExact_real
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℝ)
    {A B : E →L[ℝ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule ℝ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgapUV : DavisKahan.Sylvester.FormBoundedSylvesterGap
      (DavisKahanExt.PartialMap.boundedReducingBlock A U hU)
      (DavisKahanExt.PartialMap.boundedReducingBlockCompl B V hV) δ)
    (hgapVU : DavisKahan.Sylvester.FormBoundedSylvesterGap
      (DavisKahanExt.PartialMap.boundedReducingBlock B V hV)
      (DavisKahanExt.PartialMap.boundedReducingBlockCompl A U hU) δ)
    (hMem : N.Mem (B - A)) :
    N.Mem (V.starProjection - U.starProjection) ∧
      δ * N.gauge (V.starProjection - U.starProjection) ≤ N.gauge (B - A) :=
  normalizedUnitaryInvariant_of_symmetricNorming
    (X := V.starProjection - U.starProjection) (Y := B - A)
    N hδ hMem fun M hM =>
      proposition6_1_real M hA hB hU hV hδ hgapUV hgapVU hM

/-- **Davis--Kahan 1970, Theorem 6.1 over the literal source norm class, over
`ℂ`.**

`delta * epsilon * ‖sin Theta‖ ≤ ‖R‖` for every normalized unitarily invariant
norm, with the printed lower frame bound and spectral gap. -/
theorem theorem6_1_sourceExact_complex
    {E₀' F₀' : Type v}
    [NormedAddCommGroup E₀'] [InnerProductSpace ℂ E₀'] [CompleteSpace E₀']
    [NormedAddCommGroup F₀'] [InnerProductSpace ℂ F₀'] [CompleteSpace F₀']
    {E F G H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    (A : E →ₗ.[ℂ] E) (A₀ : F →ₗ.[ℂ] F) (Λ₁ : G →ₗ.[ℂ] G)
    (E₀ : F →L[ℂ] E) (F₀ : H →L[ℂ] E) (F₁ : G →L[ℂ] E) (R : F →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidualEquation A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {ε : ℝ} (hε : 0 < ε) (hframe : LowerFrameBound E₀ ε)
    {δ : ℝ} (hδ : 0 < δ) (hgap : DavisKahan.Sylvester.FormBoundedSylvesterGap A₀ Λ₁ δ)
    (S : SinThetaRepresentativeAcross (E₀ := E₀') (F₀ := F₀')
      (directedSinThetaOperator E₀ F₀ hframe hε))
    (hR : N.Mem R) :
    N.Mem S.operator ∧ δ * ε * N.gauge S.operator ≤ N.gauge R :=
  normalizedUnitaryInvariant_of_symmetricNorming
    (X := S.operator) (Y := R)
    N (by positivity) hR fun M hM =>
      theorem6_1_complex M A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁ htrial hexact hε hframe hδ hgap S hM

/-- **Davis--Kahan 1970, Theorem 6.1 over the literal source norm class, over
`ℝ`.**

`delta * epsilon * ‖sin Theta‖ ≤ ‖R‖` for every normalized unitarily invariant
norm, with the printed lower frame bound and spectral gap. -/
theorem theorem6_1_sourceExact_real
    {E₀' F₀' : Type v}
    [NormedAddCommGroup E₀'] [InnerProductSpace ℝ E₀'] [CompleteSpace E₀']
    [NormedAddCommGroup F₀'] [InnerProductSpace ℝ F₀'] [CompleteSpace F₀']
    {E F G H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℝ)
    (A : E →ₗ.[ℝ] E) (A₀ : F →ₗ.[ℝ] F) (Λ₁ : G →ₗ.[ℝ] G)
    (E₀ : F →L[ℝ] E) (F₀ : H →L[ℝ] E) (F₁ : G →L[ℝ] E) (R : F →L[ℝ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidualEquation A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {ε : ℝ} (hε : 0 < ε) (hframe : LowerFrameBound E₀ ε)
    {δ : ℝ} (hδ : 0 < δ) (hgap : DavisKahan.Sylvester.FormBoundedSylvesterGap A₀ Λ₁ δ)
    (S : SinThetaRepresentativeAcross (E₀ := E₀') (F₀ := F₀')
      (directedSinThetaOperatorReal E₀ F₀ hframe hε))
    (hR : N.Mem R) :
    N.Mem S.operator ∧ δ * ε * N.gauge S.operator ≤ N.gauge R :=
  normalizedUnitaryInvariant_of_symmetricNorming
    (X := S.operator) (Y := R)
    N (by positivity) hR fun M hM =>
      theorem6_1_real M A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁ htrial hexact hε hframe hδ hgap S hM

end

end DavisKahan1970
end TauCeti
