/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section6SourceNormClass
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section6AppendixLeakage
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section6AppendixLeakageReal

/-!
# Section 6 at the paper's own scope

Three things separate the Section 6 endpoints from what Davis and Kahan print,
and this module closes all three.  Nothing here is mathematics: every proof is
an application of the theorem one layer down.

**Separability.** The paper's standing ambient Hilbert space is separable, and
Theorem 6.1 does not lift that.  What Theorem 6.1 *does* relax is stated and only
that: `E₀` need only have a lower frame bound, and the compared eigenspaces may
have different dimensions.  The several Lean coordinate spaces a statement uses
are all mapped into one ambient `E`, and `E` is where the source's scope belongs;
there is no reason to decorate every coordinate space.

**The printed gap.**  `FormBoundedSylvesterGap` is a *weaker* hypothesis than the
printed one, so a theorem stated over it is a stronger theorem — and therefore
the wrong source façade.  Theorem 6.1 prints an interval/exterior separation:
one of `A₀`, `Λ₁` has spectrum in `[β, α]` and the other outside
`(β − δ, α + δ)`, with the reverse alternative also allowed.  That is exactly
`RealSpectrumIntervalExteriorGap`, and the façades below take it and build the
form-bounded gap internally.  Proposition 6.1 prints the same separation twice,
"as in the hypotheses of the `sin Θ` theorem", once for `A₀`--`Λ₁` and once for
`A₁`--`Λ₀`.

**The `sq` norm's definedness.**  Davis and Kahan's convention is that a norm
statement is vacuous when the norm does not exist, and they say they will not
keep mentioning it.  So Theorem 6.2 must not carry `R` Hilbert--Schmidt as a
hypothesis.  `theorem6_2_vacuity_sourceExact_*` states the inequality in
`ℝ≥0∞`, where a non-Hilbert--Schmidt `R` gives `⊤` on the right and the
inequality is vacuously true.  The finite-norm statement stays as the useful
nonvacuous specialization.
-/

open scoped ENNReal

namespace TauCeti
namespace DavisKahan1970

open DavisKahan
open DavisKahan.ExactSinTheta

noncomputable section

universe v

/-! ### Lemma 6.1 and Lemma 6.2 at the source's separable ambient scope -/

section Lemmas

variable {E : Type v}

/-- **Lemma 6.1 at the paper's separable ambient scope, over `ℂ`.** -/
theorem lemma6_1_separable_complex
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    (Ω Γ : Submodule ℂ E) [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K Ktilde L Ltilde : E →L[ℂ] E)
    (h₀ : ∀ M : NormalizedUnitaryInvariantNorm.{0, v} ℂ,
      M.Mem (projectionBlock Ω Γ L) →
        M.Mem (projectionBlock Ω Γ K) ∧
          M.gauge (projectionBlock Ω Γ K) ≤ M.gauge (projectionBlock Ω Γ L))
    (h₁ : ∀ M : NormalizedUnitaryInvariantNorm.{0, v} ℂ,
      M.Mem (projectionBlock Ωᗮ Γᗮ Ltilde) →
        M.Mem (projectionBlock Ωᗮ Γᗮ Ktilde) ∧
          M.gauge (projectionBlock Ωᗮ Γᗮ Ktilde) ≤
            M.gauge (projectionBlock Ωᗮ Γᗮ Ltilde))
    (hL : N.Mem (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ Ltilde)) :
    N.Mem (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ Ktilde) ∧
      N.gauge (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ Ktilde) ≤
        N.gauge (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ Ltilde) :=
  lemma6_1_sourceExact_complex N Ω Γ K Ktilde L Ltilde h₀ h₁ hL

/-- **Lemma 6.1 at the paper's separable ambient scope, over `ℝ`.** -/
theorem lemma6_1_separable_real
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℝ)
    (Ω Γ : Submodule ℝ E) [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K Ktilde L Ltilde : E →L[ℝ] E)
    (h₀ : ∀ M : NormalizedUnitaryInvariantNorm.{0, v} ℝ,
      M.Mem (projectionBlock Ω Γ L) →
        M.Mem (projectionBlock Ω Γ K) ∧
          M.gauge (projectionBlock Ω Γ K) ≤ M.gauge (projectionBlock Ω Γ L))
    (h₁ : ∀ M : NormalizedUnitaryInvariantNorm.{0, v} ℝ,
      M.Mem (projectionBlock Ωᗮ Γᗮ Ltilde) →
        M.Mem (projectionBlock Ωᗮ Γᗮ Ktilde) ∧
          M.gauge (projectionBlock Ωᗮ Γᗮ Ktilde) ≤
            M.gauge (projectionBlock Ωᗮ Γᗮ Ltilde))
    (hL : N.Mem (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ Ltilde)) :
    N.Mem (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ Ktilde) ∧
      N.gauge (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ Ktilde) ≤
        N.gauge (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ Ltilde) :=
  lemma6_1_sourceExact_real N Ω Γ K Ktilde L Ltilde h₀ h₁ hL

/-- **Lemma 6.1's converse at the paper's separable ambient scope, over `ℂ`.** -/
theorem lemma6_1_converse_separable_complex
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    (Ω Γ : Submodule ℂ E) [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K Ktilde L Ltilde : E →L[ℂ] E)
    (hK : SameApproximationSingularValues
      (projectionBlock Ω Γ K) (projectionBlock Ωᗮ Γᗮ Ktilde))
    (hL : SameApproximationSingularValues
      (projectionBlock Ω Γ L) (projectionBlock Ωᗮ Γᗮ Ltilde))
    (hsum : ∀ M : NormalizedUnitaryInvariantNorm.{0, v} ℂ,
      M.Mem (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ Ltilde) →
        M.Mem (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ Ktilde) ∧
          M.gauge (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ Ktilde) ≤
            M.gauge (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ Ltilde))
    (hLmem : N.Mem (projectionBlock Ω Γ L)) :
    N.Mem (projectionBlock Ω Γ K) ∧
      N.gauge (projectionBlock Ω Γ K) ≤ N.gauge (projectionBlock Ω Γ L) :=
  lemma6_1_converse_sourceExact_complex N Ω Γ K Ktilde L Ltilde hK hL hsum hLmem

/-- **Lemma 6.1's converse at the paper's separable ambient scope, over `ℝ`.** -/
theorem lemma6_1_converse_separable_real
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℝ)
    (Ω Γ : Submodule ℝ E) [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K Ktilde L Ltilde : E →L[ℝ] E)
    (hK : SameApproximationSingularValues
      (projectionBlock Ω Γ K) (projectionBlock Ωᗮ Γᗮ Ktilde))
    (hL : SameApproximationSingularValues
      (projectionBlock Ω Γ L) (projectionBlock Ωᗮ Γᗮ Ltilde))
    (hsum : ∀ M : NormalizedUnitaryInvariantNorm.{0, v} ℝ,
      M.Mem (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ Ltilde) →
        M.Mem (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ Ktilde) ∧
          M.gauge (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ Ktilde) ≤
            M.gauge (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ Ltilde))
    (hLmem : N.Mem (projectionBlock Ω Γ L)) :
    N.Mem (projectionBlock Ω Γ K) ∧
      N.gauge (projectionBlock Ω Γ K) ≤ N.gauge (projectionBlock Ω Γ L) :=
  lemma6_1_converse_sourceExact_real N Ω Γ K Ktilde L Ltilde hK hL hsum hLmem

/-- **Lemma 6.2 at the paper's separable ambient scope.** -/
theorem lemma6_2_separable {𝕜 : Type} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    
    (N : NormalizedUnitaryInvariantNorm.{0, v} 𝕜)
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {K : E →L[𝕜] E} (hK : N.Mem K) :
    N.Mem (diagonalPair U V K) ∧ N.gauge (diagonalPair U V K) ≤ N.gauge K :=
  lemma6_2_sourceExact N U V hK

end Lemmas

/-! ### Proposition 6.1 and Theorem 6.1 on the printed separation -/

section PrintedGap

/-- **Davis--Kahan 1970, Proposition 6.1 at the printed source scope, over `ℂ`.**

The separation is the `sin Θ` theorem's own interval/exterior hypothesis, taken
twice as the source takes it, and the ambient space is separable. -/
theorem proposition6_1_printedGap_sourceExact_complex
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    {A B : E →L[ℂ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {δ : ℝ} (hδ : 0 < δ)
    {β α β' α' : ℝ} (hβα : β ≤ α) (hβα' : β' ≤ α')
    (hgapUV : DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap
      (DavisKahanExt.PartialMap.boundedReducingBlock A U hU)
      (DavisKahanExt.PartialMap.boundedReducingBlockCompl B V hV) β α δ)
    (hgapVU : DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap
      (DavisKahanExt.PartialMap.boundedReducingBlock B V hV)
      (DavisKahanExt.PartialMap.boundedReducingBlockCompl A U hU) β' α' δ)
    (hMem : N.Mem (B - A)) :
    N.Mem (DavisKahan.Angle.sinAngleOperatorC U V) ∧
      δ * N.gauge (DavisKahan.Angle.sinAngleOperatorC U V) ≤ N.gauge (B - A) :=
  proposition6_1_sourceExact_complex N hA hB hU hV hδ
    (.intervalExterior hβα hgapUV) (.intervalExterior hβα' hgapVU) hMem

/-- **Davis--Kahan 1970, Proposition 6.1 at the printed source scope, over `ℝ`.** -/
theorem proposition6_1_printedGap_sourceExact_real
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℝ)
    {A B : E →L[ℝ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule ℝ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {δ : ℝ} (hδ : 0 < δ)
    {β α β' α' : ℝ} (hβα : β ≤ α) (hβα' : β' ≤ α')
    (hgapUV : DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap
      (DavisKahanExt.PartialMap.boundedReducingBlock A U hU)
      (DavisKahanExt.PartialMap.boundedReducingBlockCompl B V hV) β α δ)
    (hgapVU : DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap
      (DavisKahanExt.PartialMap.boundedReducingBlock B V hV)
      (DavisKahanExt.PartialMap.boundedReducingBlockCompl A U hU) β' α' δ)
    (hMem : N.Mem (B - A)) :
    N.Mem (V.starProjection - U.starProjection) ∧
      δ * N.gauge (V.starProjection - U.starProjection) ≤ N.gauge (B - A) :=
  proposition6_1_sourceExact_real N hA hB hU hV hδ
    (.intervalExterior hβα hgapUV) (.intervalExterior hβα' hgapVU) hMem

end PrintedGap

/-! ### Theorem 6.1 on the printed separation -/

section Theorem61Printed

variable {E₀' F₀' : Type v} {E F G H : Type v}

/-- **Davis--Kahan 1970, Theorem 6.1 at the printed source scope, over `ℂ`.**

"If one of `A₀`, `Λ₁` has spectrum in `[β, α]` and the other has spectrum
outside `(β − δ, α + δ)`" — the printed separation, not the weaker form-bounded
abstraction the proof runs on — on the paper's separable ambient space. -/
theorem theorem6_1_printedGap_sourceExact_complex
    [NormedAddCommGroup E₀'] [InnerProductSpace ℂ E₀'] [CompleteSpace E₀']
    [NormedAddCommGroup F₀'] [InnerProductSpace ℂ F₀'] [CompleteSpace F₀']
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
    {δ : ℝ} (hδ : 0 < δ) {β α : ℝ} (hβα : β ≤ α)
    (hgap : DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap A₀ Λ₁ β α δ)
    (S : SinThetaRepresentativeAcross (E₀ := E₀') (F₀ := F₀')
      (directedSinThetaOperator E₀ F₀ hframe hε))
    (hR : N.Mem R) :
    N.Mem S.operator ∧ δ * ε * N.gauge S.operator ≤ N.gauge R :=
  theorem6_1_sourceExact_complex N A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁ htrial hexact hε
    hframe hδ (.intervalExterior hβα hgap) S hR

/-- **Davis--Kahan 1970, Theorem 6.1 at the printed source scope, over `ℝ`.** -/
theorem theorem6_1_printedGap_sourceExact_real
    [NormedAddCommGroup E₀'] [InnerProductSpace ℝ E₀'] [CompleteSpace E₀']
    [NormedAddCommGroup F₀'] [InnerProductSpace ℝ F₀'] [CompleteSpace F₀']
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
    {δ : ℝ} (hδ : 0 < δ) {β α : ℝ} (hβα : β ≤ α)
    (hgap : DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap A₀ Λ₁ β α δ)
    (S : SinThetaRepresentativeAcross (E₀ := E₀') (F₀ := F₀')
      (directedSinThetaOperatorReal E₀ F₀ hframe hε))
    (hR : N.Mem R) :
    N.Mem S.operator ∧ δ * ε * N.gauge S.operator ≤ N.gauge R :=
  theorem6_1_sourceExact_real N A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁ htrial hexact hε
    hframe hδ (.intervalExterior hβα hgap) S hR

end Theorem61Printed

/-! ### Theorem 6.2 under the source's definedness convention -/

section Theorem62Vacuity

variable {E₀' F₀' : Type v} {E F G H : Type v}

/-- Finiteness of the Hilbert--Schmidt energy and of the Hilbert--Schmidt
`ℝ≥0∞`-norm are the same condition. -/
private theorem energy_ne_top_iff_hilbertSchmidtENorm_ne_top
    {𝕜 : Type} [RCLike 𝕜] {X Y : Type v}
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [CompleteSpace Y]
    (T : X →L[𝕜] Y) :
    approximationNumberEnergy T ≠ ⊤ ↔ T.hilbertSchmidtENorm ≠ ⊤ := by
  rw [approximationNumberEnergy_eq_hilbertSchmidtENorm_sq]
  constructor
  · intro h hT
    exact h (by rw [hT, ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < 2)])
  · intro h
    exact (ENNReal.rpow_ne_top_of_nonneg (by norm_num) h)

/-- The `ℝ≥0∞` reading of a finite Hilbert--Schmidt estimate. -/
private theorem enorm_le_of_hilbertSchmidtNorm_le
    {𝕜 : Type} [RCLike 𝕜] {X Y X' Y' : Type v}
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] 
    [NormedAddCommGroup X'] [InnerProductSpace 𝕜 X'] [CompleteSpace X']
    [NormedAddCommGroup Y'] [InnerProductSpace 𝕜 Y'] 
    {S : X →L[𝕜] Y} {R : X' →L[𝕜] Y'} {c : ℝ} (hc : 0 ≤ c)
    (hS : S.hilbertSchmidtENorm ≠ ⊤) (hR : R.hilbertSchmidtENorm ≠ ⊤)
    (h : c * S.hilbertSchmidtNorm ≤ R.hilbertSchmidtNorm) :
    ENNReal.ofReal c * S.hilbertSchmidtENorm ≤ R.hilbertSchmidtENorm := by
  rw [← ENNReal.ofReal_toReal hS, ← ENNReal.ofReal_toReal hR,
    ← ENNReal.ofReal_mul hc]
  exact ENNReal.ofReal_le_ofReal
    (by simpa [ContinuousLinearMap.hilbertSchmidtNorm_eq_toReal] using h)

/-- **Davis--Kahan 1970, Theorem 6.2 under the source's definedness convention,
over `ℂ`.**

`δ ε ‖sin Θ₀‖_sq ≤ ‖R‖_sq` with **no** hypothesis that `R` is
Hilbert--Schmidt.  Davis and Kahan say a norm statement is vacuous when the norm
does not exist and that they will not keep saying so; in `ℝ≥0∞` that is literal —
a non-Hilbert--Schmidt `R` makes the right-hand side `⊤`.
`theorem6_2_complex` is the same estimate on the finite norms, which is the
nonvacuous case. -/
theorem theorem6_2_vacuity_sourceExact_complex
    [NormedAddCommGroup E₀'] [InnerProductSpace ℂ E₀'] [CompleteSpace E₀']
    [NormedAddCommGroup F₀'] [InnerProductSpace ℂ F₀'] [CompleteSpace F₀']
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : E →ₗ.[ℂ] E) (A₀ : F →ₗ.[ℂ] F) (Λ₁ : G →ₗ.[ℂ] G)
    (E₀ : F →L[ℂ] E) (F₀ : H →L[ℂ] E) (F₁ : G →L[ℂ] E) (R : F →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidualEquation A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {ε : ℝ} (hε : 0 < ε) (hframe : LowerFrameBound E₀ ε)
    {δ : ℝ} (hδ : 0 < δ) (hdist : PairwiseSpectrumGap A₀ Λ₁ δ)
    (S : SinThetaRepresentativeAcross (E₀ := E₀') (F₀ := F₀')
      (sectionSixSinThetaBlock E₀ F₁ hframe hε)) :
    ENNReal.ofReal (δ * ε) * S.operator.hilbertSchmidtENorm ≤ R.hilbertSchmidtENorm := by
  rcases eq_or_ne R.hilbertSchmidtENorm ⊤ with hRtop | hRne
  · rw [hRtop]; exact le_top
  obtain ⟨hSne, hle⟩ := theorem6_2_complex A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁ htrial hexact
    hε hframe hδ hdist S ((energy_ne_top_iff_hilbertSchmidtENorm_ne_top R).mpr hRne)
  exact enorm_le_of_hilbertSchmidtNorm_le (by positivity)
    ((energy_ne_top_iff_hilbertSchmidtENorm_ne_top S.operator).mp hSne) hRne hle

/-- **Davis--Kahan 1970, Theorem 6.2 under the source's definedness convention,
over `ℝ`.** -/
theorem theorem6_2_vacuity_sourceExact_real
    [NormedAddCommGroup E₀'] [InnerProductSpace ℝ E₀'] [CompleteSpace E₀']
    [NormedAddCommGroup F₀'] [InnerProductSpace ℝ F₀'] [CompleteSpace F₀']
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : E →ₗ.[ℝ] E) (A₀ : F →ₗ.[ℝ] F) (Λ₁ : G →ₗ.[ℝ] G)
    (E₀ : F →L[ℝ] E) (F₀ : H →L[ℝ] E) (F₁ : G →L[ℝ] E) (R : F →L[ℝ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidualEquation A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {ε : ℝ} (hε : 0 < ε) (hframe : LowerFrameBound E₀ ε)
    {δ : ℝ} (hδ : 0 < δ)
    (hdist : ∀ lam ∈ TauCeti.LinearPMap.realSpectrum A₀,
      ∀ α ∈ TauCeti.LinearPMap.realSpectrum Λ₁, δ ≤ |lam - α|)
    (S : SinThetaRepresentativeAcross (E₀ := E₀') (F₀ := F₀')
      (sectionSixSinThetaBlockReal E₀ F₁ hframe hε)) :
    ENNReal.ofReal (δ * ε) * S.operator.hilbertSchmidtENorm ≤ R.hilbertSchmidtENorm := by
  rcases eq_or_ne R.hilbertSchmidtENorm ⊤ with hRtop | hRne
  · rw [hRtop]; exact le_top
  obtain ⟨hSne, hle⟩ := theorem6_2_real A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁ htrial hexact
    hε hframe hδ hdist S ((energy_ne_top_iff_hilbertSchmidtENorm_ne_top R).mpr hRne)
  exact enorm_le_of_hilbertSchmidtNorm_le (by positivity)
    ((energy_ne_top_iff_hilbertSchmidtENorm_ne_top S.operator).mp hSne) hRne hle

end Theorem62Vacuity

/-! ### Lemma 6.3 at the source's separable ambient scope -/

section Lemma63

/-- **Lemma 6.3 at the paper's separable ambient scope, over `ℂ`.** -/
theorem lemma6_3_leakage_separable_complex {E' F' : Type v}
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
    
    (K : E' →L[ℂ] F')
    (P : Submodule ℂ E') [P.HasOrthogonalProjection]
    (Q : Submodule ℂ F') [Q.HasOrthogonalProjection]
    (n : ℕ) (hn : 0 < n) (η : ℝ) (hη : 0 < η)
    (hKP : K ∘L P.starProjection = Q.starProjection ∘L K ∘L P.starProjection)
    (hrankP : P.starProjection.rank ≤ (n : Cardinal))
    (hrankQ : Q.starProjection.rank ≤ (n : Cardinal))
    (hnear : Section6Appendix.approximationEnergy (K ∘L P.starProjection) n >
      Section6Appendix.approximationEnergy K n - η ^ 2) :
    ‖Q.starProjection ∘L K ∘L (1 - P.starProjection)‖ < η :=
  Section6Appendix.lemma6_3_approximationNumber_leakage_complex K P Q n hn η hη hKP
    hrankP hrankQ hnear

/-- **Lemma 6.3 at the paper's separable ambient scope, over `ℝ`.** -/
theorem lemma6_3_leakage_separable_real {E' F' : Type v}
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [CompleteSpace E']
    
    [NormedAddCommGroup F'] [InnerProductSpace ℝ F'] [CompleteSpace F']
    
    (K : E' →L[ℝ] F')
    (P : Submodule ℝ E') [P.HasOrthogonalProjection]
    (Q : Submodule ℝ F') [Q.HasOrthogonalProjection]
    (n : ℕ) (hn : 0 < n) (η : ℝ) (hη : 0 < η)
    (hKP : K ∘L P.starProjection = Q.starProjection ∘L K ∘L P.starProjection)
    (hrankP : P.starProjection.rank ≤ (n : Cardinal))
    (hrankQ : Q.starProjection.rank ≤ (n : Cardinal))
    (hnear : Section6Appendix.approximationEnergy (K ∘L P.starProjection) n >
      Section6Appendix.approximationEnergy K n - η ^ 2) :
    ‖Q.starProjection ∘L K ∘L (1 - P.starProjection)‖ < η :=
  Section6Appendix.lemma6_3_approximationNumber_leakage_real K P Q n hn η hη hKP
    hrankP hrankQ hnear

end Lemma63

/-! ### Lemma 6.1 with the source's own two operators

Davis and Kahan's Lemma 6.1 compares **one** `K` with **one** `L`: the hypothesis
is `‖Ω K Υ‖ ≤ ‖Ω L Υ‖` together with `‖Ωᗮ K Υᗮ‖ ≤ ‖Ωᗮ L Υᗮ‖`, and the conclusion
is the same inequality for the sum of the two diagonal blocks *of those two
operators*.  The four-operator statements above let the two blocks come from
different operators; that is a strictly stronger theorem and the wrong signature
for a source boundary.  These are the printed ones. -/

section LemmaSixOneTwoOperators

variable {E : Type v}

/-- **Davis--Kahan 1970, Lemma 6.1 on the source's two operators, over `ℂ`.** -/
theorem lemma6_1_sourceOperators_separable_complex
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    (Ω Γ : Submodule ℂ E) [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K L : E →L[ℂ] E)
    (h₀ : ∀ M : NormalizedUnitaryInvariantNorm.{0, v} ℂ,
      M.Mem (projectionBlock Ω Γ L) →
        M.Mem (projectionBlock Ω Γ K) ∧
          M.gauge (projectionBlock Ω Γ K) ≤ M.gauge (projectionBlock Ω Γ L))
    (h₁ : ∀ M : NormalizedUnitaryInvariantNorm.{0, v} ℂ,
      M.Mem (projectionBlock Ωᗮ Γᗮ L) →
        M.Mem (projectionBlock Ωᗮ Γᗮ K) ∧
          M.gauge (projectionBlock Ωᗮ Γᗮ K) ≤ M.gauge (projectionBlock Ωᗮ Γᗮ L))
    (hL : N.Mem (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ L)) :
    N.Mem (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ K) ∧
      N.gauge (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ K) ≤
        N.gauge (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ L) :=
  lemma6_1_separable_complex N Ω Γ K K L L h₀ h₁ hL

/-- **Davis--Kahan 1970, Lemma 6.1 on the source's two operators, over `ℝ`.** -/
theorem lemma6_1_sourceOperators_separable_real
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℝ)
    (Ω Γ : Submodule ℝ E) [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K L : E →L[ℝ] E)
    (h₀ : ∀ M : NormalizedUnitaryInvariantNorm.{0, v} ℝ,
      M.Mem (projectionBlock Ω Γ L) →
        M.Mem (projectionBlock Ω Γ K) ∧
          M.gauge (projectionBlock Ω Γ K) ≤ M.gauge (projectionBlock Ω Γ L))
    (h₁ : ∀ M : NormalizedUnitaryInvariantNorm.{0, v} ℝ,
      M.Mem (projectionBlock Ωᗮ Γᗮ L) →
        M.Mem (projectionBlock Ωᗮ Γᗮ K) ∧
          M.gauge (projectionBlock Ωᗮ Γᗮ K) ≤ M.gauge (projectionBlock Ωᗮ Γᗮ L))
    (hL : N.Mem (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ L)) :
    N.Mem (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ K) ∧
      N.gauge (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ K) ≤
        N.gauge (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ L) :=
  lemma6_1_separable_real N Ω Γ K K L L h₀ h₁ hL

/-- **Lemma 6.1's converse on the source's two operators, over `ℂ`.**

The printed converse compares the two diagonal blocks *of `K`* and *of `L`*: each
operator's two blocks are equisingular, and the sum inequality is assumed. -/
theorem lemma6_1_converse_sourceOperators_separable_complex
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    (Ω Γ : Submodule ℂ E) [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K L : E →L[ℂ] E)
    (hK : SameApproximationSingularValues
      (projectionBlock Ω Γ K) (projectionBlock Ωᗮ Γᗮ K))
    (hL : SameApproximationSingularValues
      (projectionBlock Ω Γ L) (projectionBlock Ωᗮ Γᗮ L))
    (hsum : ∀ M : NormalizedUnitaryInvariantNorm.{0, v} ℂ,
      M.Mem (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ L) →
        M.Mem (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ K) ∧
          M.gauge (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ K) ≤
            M.gauge (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ L))
    (hLmem : N.Mem (projectionBlock Ω Γ L)) :
    N.Mem (projectionBlock Ω Γ K) ∧
      N.gauge (projectionBlock Ω Γ K) ≤ N.gauge (projectionBlock Ω Γ L) :=
  lemma6_1_converse_separable_complex N Ω Γ K K L L hK hL hsum hLmem

/-- **Lemma 6.1's converse on the source's two operators, over `ℝ`.** -/
theorem lemma6_1_converse_sourceOperators_separable_real
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℝ)
    (Ω Γ : Submodule ℝ E) [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K L : E →L[ℝ] E)
    (hK : SameApproximationSingularValues
      (projectionBlock Ω Γ K) (projectionBlock Ωᗮ Γᗮ K))
    (hL : SameApproximationSingularValues
      (projectionBlock Ω Γ L) (projectionBlock Ωᗮ Γᗮ L))
    (hsum : ∀ M : NormalizedUnitaryInvariantNorm.{0, v} ℝ,
      M.Mem (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ L) →
        M.Mem (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ K) ∧
          M.gauge (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ K) ≤
            M.gauge (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ L))
    (hLmem : N.Mem (projectionBlock Ω Γ L)) :
    N.Mem (projectionBlock Ω Γ K) ∧
      N.gauge (projectionBlock Ω Γ K) ≤ N.gauge (projectionBlock Ω Γ L) :=
  lemma6_1_converse_separable_real N Ω Γ K K L L hK hL hsum hLmem

end LemmaSixOneTwoOperators

end

end DavisKahan1970
end TauCeti
