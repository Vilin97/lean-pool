/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
module

public import LeanPool.Malliavin.Malliavin.PointwiseCondExp

/-!
# Left-continuity modulo null sets of the natural Brownian filtration

The raw natural filtration need not be literally left-continuous: changing `B t` on a null set
can change its generated sigma-algebra.  Conditional expectations only see sigma-algebras modulo
null sets.  This file proves the appropriate statement:

`P[X | 𝓕_{t⁻}] =ᵐ[P] P[X | 𝓕_t]`

for the natural filtration of a pre-Brownian process and every positive `t`.

The proof takes a subsequence of the `L²` convergence `B_{t-t/(n+2)} → B_t`, uses its measurable
pointwise `limsup` as a strict-past version of `B_t`, and observes that the natural sigma-algebra
at `t` is the strict past joined with `B_t`.  Conditional-expectation uniqueness then gives the
claim.  Combining it with `PointwiseCondExp.lean` yields the literal textbook
`E[DₜF | 𝓕_t]` representative of the Clark--Ocone integrand.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace

namespace Malliavin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]

omit [CompleteSpace W] [BorelSpace W] in
/-- If every event at time `t` has a strict-past-measurable representative modulo `P`, then
conditioning on the strict past and conditioning at `t` agree. -/
theorem condExp_filtrationPred_ae_eq_of_ae_sets
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0)
    (hcomplete : ∀ s : Set W, MeasurableSet[𝓕 t] s →
      ∃ r : Set W, MeasurableSet[filtrationPred 𝓕 t] r ∧ s =ᵐ[P] r)
    (X : W → ℝ) (hX : Integrable X P) :
    P[X | filtrationPred 𝓕 t] =ᵐ[P] P[X | 𝓕 t] := by
  let Y : W → ℝ := P[X | filtrationPred 𝓕 t]
  have hpredt : filtrationPred 𝓕 t ≤ 𝓕 t :=
    iSup₂_le fun u (hut : u < t) ↦ 𝓕.mono hut.le
  apply ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le t) hX
  · intro s _ _
    exact integrable_condExp.integrableOn
  · intro s hs _
    obtain ⟨r, hr, hsr⟩ := hcomplete s hs
    calc
      ∫ x in s, Y x ∂P = ∫ x in r, Y x ∂P := setIntegral_congr_set hsr
      _ = ∫ x in r, X x ∂P := setIntegral_condExp (filtrationPred_le 𝓕 t) hX hr
      _ = ∫ x in s, X x ∂P := (setIntegral_congr_set hsr).symm
  · exact (stronglyMeasurable_condExp.mono hpredt).aestronglyMeasurable

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The endpoint coordinate `B t` has a strict-past-measurable version for every `t > 0`. -/
theorem aestronglyMeasurable_brownian_filtrationPred
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ s, StronglyMeasurable (B s)) (t : ℝ≥0) (ht : 0 < t) :
    AEStronglyMeasurable[filtrationPred (Filtration.natural B hm) t] (B t) P := by
  let u : ℕ → ℝ≥0 := fun n ↦ t - t / (n + 2)
  have hu_lt : ∀ n, u n < t := fun n ↦ tsub_lt_self ht (by positivity)
  have hconv : TendstoInMeasure P
      (fun n : ℕ ↦ (brownianLp hB (u n) : W → ℝ)) atTop
      (brownianLp hB t : W → ℝ) :=
    tendstoInMeasure_of_tendsto_Lp (tendsto_brownianLp_exhaustion hB t)
  obtain ⟨ns, -, hlim⟩ := hconv.exists_seq_tendsto_ae
  have hcoe : ∀ᵐ w ∂P, ∀ n,
      (brownianLp hB (u (ns n)) : W → ℝ) w = B (u (ns n)) w :=
    ae_all_iff.2 fun n ↦ coeFn_brownianLp hB _
  have hlimB : ∀ᵐ w ∂P,
      Tendsto (fun n ↦ B (u (ns n)) w) atTop (nhds (B t w)) := by
    filter_upwards [hlim, hcoe, coeFn_brownianLp hB t] with w hw hcw htw
    simpa only [hcw, htw] using hw
  let G : W → ℝ := fun w ↦ limsup (fun n ↦ B (u (ns n)) w) atTop
  have hG : StronglyMeasurable[filtrationPred (Filtration.natural B hm) t] G :=
    Measurable.stronglyMeasurable (Measurable.limsup fun n ↦
      ((Filtration.stronglyAdapted_natural hm (u (ns n))).mono
        (le_filtrationPred (Filtration.natural B hm) (hu_lt (ns n)))).measurable)
  exact hG.aestronglyMeasurable.congr (hlimB.mono fun w hw ↦ hw.limsup_eq)

omit [CompleteSpace W] [BorelSpace W] in
/-- **Left-continuity modulo `P` of the natural Brownian filtration.** -/
theorem condExp_natural_filtrationPred_ae_eq
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ s, StronglyMeasurable (B s)) (t : ℝ≥0) (ht : 0 < t)
    (X : W → ℝ) (hX : Integrable X P) :
    P[X | filtrationPred (Filtration.natural B hm) t] =ᵐ[P]
      P[X | Filtration.natural B hm t] := by
  have hBt : AEStronglyMeasurable[filtrationPred (Filtration.natural B hm) t] (B t) P :=
    aestronglyMeasurable_brownian_filtrationPred hB hm t ht
  have hBtEventually : EventuallyMeasurable
      (filtrationPred (Filtration.natural B hm) t) (ae P) (B t) :=
    hBt.stronglyMeasurable_mk.measurable.eventuallyMeasurable.congr hBt.ae_eq_mk
  have hNaturalCompletion : Filtration.natural B hm t ≤
      eventuallyMeasurableSpace (filtrationPred (Filtration.natural B hm) t) (ae P) := by
    rw [natural_eq_filtrationPred_sup hm t]
    exact sup_le le_eventuallyMeasurableSpace hBtEventually.comap_le
  apply condExp_filtrationPred_ae_eq_of_ae_sets (Filtration.natural B hm) t
  · intro s hs
    exact hNaturalCompletion s hs
  · exact hX

section ClarkOcone

variable {B : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}

/-- A Clark--Ocone family's natural filtration is left-continuous at the level of conditional
expectations. -/
theorem ClarkOconeFamily.condExp_filtrationPred_ae_eq
    (C : ClarkOconeFamily B P 𝓕) (t : ℝ≥0) (ht : 0 < t)
    (X : W → ℝ) (hX : Integrable X P) :
    P[X | filtrationPred 𝓕 t] =ᵐ[P] P[X | 𝓕 t] := by
  rw [C.naturalFiltration]
  exact condExp_natural_filtrationPred_ae_eq
    C.isPreBrownian C.stronglyMeasurable t ht X hX

/-- **Literal textbook Clark--Ocone integrand.**  For every `F ∈ 𝔻₁,₂`, the predictable
derivative has a predictable representative whose section is `E[DₜF | 𝓕_t]` for almost every
positive time. -/
theorem exists_representative_predictableDerivative_condExp_natural
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    ∃ G : ℝ≥0 × W → ℝ,
      StronglyMeasurable[𝓕.predictable] G ∧
      (predictableDerivative C F : ℝ≥0 × W → ℝ)
        =ᵐ[nonnegativeLebesgueMeasure.prod P] G ∧
      ∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
        (fun w ↦ G (t, w)) =ᵐ[P]
          P[(fun w ↦ (C.timeDerivative (mderivD12 P F)) (t, w)) | 𝓕 t] := by
  apply exists_representative_predictableDerivative_condExp_of_condExp_leftContinuous C F
  intro t ht X hX
  exact C.condExp_filtrationPred_ae_eq t ht X hX

/-- Kernel form of the textbook Clark--Ocone integrand: the representative is the integral of
the time section of the Malliavin derivative against `condExpKernel P (𝓕 t)`. -/
theorem exists_representative_predictableDerivative_integral_condExpKernel_natural
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    ∃ G : ℝ≥0 × W → ℝ,
      StronglyMeasurable[𝓕.predictable] G ∧
      (predictableDerivative C F : ℝ≥0 × W → ℝ)
        =ᵐ[nonnegativeLebesgueMeasure.prod P] G ∧
      ∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
        (fun w ↦ G (t, w)) =ᵐ[P]
          fun w ↦ ∫ y, (C.timeDerivative (mderivD12 P F)) (t, y)
            ∂condExpKernel P (𝓕 t) w := by
  obtain ⟨G, hG, hGae, hsection⟩ :=
    exists_representative_predictableDerivative_condExp_natural C F
  refine ⟨G, hG, hGae, ?_⟩
  filter_upwards [hsection,
    condExp_timeSection_ae_eq_integral_condExpKernel 𝓕
      (C.timeDerivative (mderivD12 P F))] with t hsection_t hkernel_t ht
  exact (hsection_t ht).trans hkernel_t

end ClarkOcone

end Malliavin

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
