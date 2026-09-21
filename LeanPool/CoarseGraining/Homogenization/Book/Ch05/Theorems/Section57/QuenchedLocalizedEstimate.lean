/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.MinimalScaleTail

/-! # Quenched Localized Estimate -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open Filter
open scoped ENNReal
open scoped Topology

/-!
# Localized estimate above the quantitative minimal scale

This file connects the abstract bad-tail minimal scale to the concrete
finite-probe envelope.  The stochastic input is the almost-sure good-tail
event for the bad scales; the tail estimate for the same scale is supplied in
`MinimalScaleTail`.
-/

noncomputable section

/-- Shifted localized quenched estimate above the tail-based minimal scale. -/
theorem quenchedLocalizedEstimate_shifted_above_quenchedMinimalScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {t α : ℝ} {Nentry Nmin : ℕ}
    (hgoodAE :
      let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
        fun M N aω =>
          quenchedProbeEnvelope hP hStruct (Nentry + M) (Nentry + N) aω
      ∀ᵐ aω ∂P, hasGoodTailFrom Nmin (badScaleEvent Hshift t α) aω) :
    let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
      fun M N aω =>
        quenchedProbeEnvelope hP hStruct (Nentry + M) (Nentry + N) aω
    let Bad : ℕ → Set (RegCoeffField d) := badScaleEvent Hshift t α
    let X : RegCoeffField d → ℝ := quenchedMinimalScale Nmin Bad
    (∀ aω, 1 ≤ X aω) ∧
      ∀ (e : FullBlockVec d), dotProduct e e ≤ 1 →
        ∀ᵐ aω ∂P,
          ∀ {m n : ℕ},
            X aω ≤ (3 : ℝ) ^ m →
            n < m →
            (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) *
                localizedLimitNormalizedJMax hP hStruct
                  (Nentry + m) (Nentry + n) e aω ≤
              ((3 : ℝ) ^ m / X aω) ^ (-α) := by
  intro Hshift Bad X
  refine ⟨?_, ?_⟩
  · intro aω
    simpa [X] using one_le_quenchedMinimalScale Nmin Bad aω
  · intro e he
    have hgoodAE' : ∀ᵐ aω ∂P, hasGoodTailFrom Nmin Bad aω := by
      simpa [Hshift, Bad] using hgoodAE
    have hfinite :
        ∀ᵐ aω ∂P, ∀ m n : ℕ, n ≤ m →
          localizedLimitNormalizedJMax hP hStruct
              (Nentry + m) (Nentry + n) e aω ≤
            Hshift m n aω := by
      rw [MeasureTheory.ae_all_iff]
      intro m
      rw [MeasureTheory.ae_all_iff]
      intro n
      by_cases hnm : n ≤ m
      · have habs : Nentry + n ≤ Nentry + m :=
          Nat.add_le_add_left hnm Nentry
        exact
          (localizedLimitNormalizedJMax_le_quenchedProbeEnvelope_ae
            hP hStruct hΓ habs e he).mono fun aω hle _ => by
              simpa [Hshift, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hle
      · exact Filter.Eventually.of_forall fun _ hnm' => False.elim (hnm hnm')
    filter_upwards [hgoodAE', hfinite] with aω hgood hfinite_a
    intro m n hscale hnm
    have henv :
        (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) * Hshift m n aω ≤
          ((3 : ℝ) ^ m / X aω) ^ (-α) := by
      simpa [Bad, X] using
        badScaleEvent_estimate_above_quenchedMinimalScale
          (N0 := Nmin) (H := Hshift) (t := t) (α := α)
          (ω := aω) hgood (m := m) (n := n)
          (by simpa [Bad, X] using hscale) hnm
    have hpoint :
        localizedLimitNormalizedJMax hP hStruct
            (Nentry + m) (Nentry + n) e aω ≤
          Hshift m n aω :=
      hfinite_a m n (le_of_lt hnm)
    exact (mul_le_mul_of_nonneg_left hpoint
      (by positivity : 0 ≤ (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)))).trans henv

/-- Tail-bound form of the shifted localized estimate.  The two hypotheses on
`badTailEvent` are the exact quantitative inputs produced by the bad-scale
summation step: one gives the stochastic integrability of `X`, the other
removes the null exceptional set with no good tail. -/
theorem quenchedLocalizedEstimate_shifted_from_badTailBounds
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {t α η B : ℝ} {Nentry Nmin : ℕ}
    (hη_pos : 0 < η) (hB : 1 ≤ B)
    (hsmall :
      let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
        fun M N aω =>
          quenchedProbeEnvelope hP hStruct (Nentry + M) (Nentry + N) aω
      let Bad : ℕ → Set (RegCoeffField d) := badScaleEvent Hshift t α
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, Nmin ≤ N ∧ P.real (badTailEvent Bad N) ≤ ε)
    (htail :
      let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
        fun M N aω =>
          quenchedProbeEnvelope hP hStruct (Nentry + M) (Nentry + N) aω
      let Bad : ℕ → Set (RegCoeffField d) := badScaleEvent Hshift t α
      ∀ N : ℕ, Nmin ≤ N →
        P.real (badTailEvent Bad N) ≤
          Real.exp
            (-(((Real.rpow (3 : ℝ) ((N - Nmin : ℕ) : ℝ)) / B) ^ η))) :
    let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
      fun M N aω =>
        quenchedProbeEnvelope hP hStruct (Nentry + M) (Nentry + N) aω
    let Bad : ℕ → Set (RegCoeffField d) := badScaleEvent Hshift t α
    let X : RegCoeffField d → ℝ := quenchedMinimalScale Nmin Bad
    IsBigO P (gammaSigma η) X
      (3 * ((3 : ℝ) ^ Nmin) * B) ∧
      (∀ aω, 1 ≤ X aω) ∧
        ∀ (e : FullBlockVec d), dotProduct e e ≤ 1 →
          ∀ᵐ aω ∂P,
            ∀ {m n : ℕ},
              X aω ≤ (3 : ℝ) ^ m →
              n < m →
              (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) *
                  localizedLimitNormalizedJMax hP hStruct
                    (Nentry + m) (Nentry + n) e aω ≤
                ((3 : ℝ) ^ m / X aω) ^ (-α) := by
  intro Hshift Bad X
  let : IsProbabilityMeasure P := hP.isProbability
  have hgoodAE : ∀ᵐ aω ∂P, hasGoodTailFrom Nmin Bad aω := by
    exact ae_hasGoodTailFrom
      (μ := P) (N0 := Nmin) (Bad := Bad) (by simpa [Hshift, Bad] using hsmall)
  have hlocalized :=
    quenchedLocalizedEstimate_shifted_above_quenchedMinimalScale
      hP hStruct hΓ (t := t) (α := α)
      (Nentry := Nentry) (Nmin := Nmin)
      (by simpa [Hshift, Bad] using hgoodAE)
  have htailX :
      IsBigO P (gammaSigma η) X (3 * ((3 : ℝ) ^ Nmin) * B) := by
    simpa [X] using
      isBigO_quenchedMinimalScale_of_badTailEvent_bound
        (μ := P) (N0 := Nmin) (Bad := Bad) (B := B) (η := η)
        hη_pos hB (by simpa [Hshift, Bad] using htail)
  exact ⟨htailX, by simpa [Hshift, Bad, X] using hlocalized⟩

/-- Version of `quenchedLocalizedEstimate_shifted_from_badTailBounds` whose
quantitative input is stated directly for the manuscript bad-scale events.
Since `badScaleEvent H t α` is antitone in the bad scale for `0 ≤ α`, the
tail event over all later bad scales is contained in the bad-scale event at
the first level. -/
theorem quenchedLocalizedEstimate_shifted_from_badScaleBounds
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {t α η B : ℝ} {Nentry Nmin : ℕ}
    (hα_nonneg : 0 ≤ α) (hη_pos : 0 < η) (hB : 1 ≤ B)
    (hsmall :
      let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
        fun M N aω =>
          quenchedProbeEnvelope hP hStruct (Nentry + M) (Nentry + N) aω
      let Bad : ℕ → Set (RegCoeffField d) := badScaleEvent Hshift t α
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, Nmin ≤ N ∧ P.real (Bad N) ≤ ε)
    (htail :
      let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
        fun M N aω =>
          quenchedProbeEnvelope hP hStruct (Nentry + M) (Nentry + N) aω
      let Bad : ℕ → Set (RegCoeffField d) := badScaleEvent Hshift t α
      ∀ N : ℕ, Nmin ≤ N →
        P.real (Bad N) ≤
          Real.exp
            (-(((Real.rpow (3 : ℝ) ((N - Nmin : ℕ) : ℝ)) / B) ^ η))) :
    let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
      fun M N aω =>
        quenchedProbeEnvelope hP hStruct (Nentry + M) (Nentry + N) aω
    let Bad : ℕ → Set (RegCoeffField d) := badScaleEvent Hshift t α
    let X : RegCoeffField d → ℝ := quenchedMinimalScale Nmin Bad
    IsBigO P (gammaSigma η) X
      (3 * ((3 : ℝ) ^ Nmin) * B) ∧
      (∀ aω, 1 ≤ X aω) ∧
        ∀ (e : FullBlockVec d), dotProduct e e ≤ 1 →
          ∀ᵐ aω ∂P,
            ∀ {m n : ℕ},
              X aω ≤ (3 : ℝ) ^ m →
              n < m →
              (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) *
                  localizedLimitNormalizedJMax hP hStruct
                    (Nentry + m) (Nentry + n) e aω ≤
                ((3 : ℝ) ^ m / X aω) ^ (-α) := by
  intro Hshift Bad X
  let : IsProbabilityMeasure P := hP.isProbability
  have hsmall_tail :
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, Nmin ≤ N ∧ P.real (badTailEvent Bad N) ≤ ε := by
    intro ε hε
    obtain ⟨N, hNmin, hN⟩ := by
      simpa [Hshift, Bad] using hsmall ε hε
    refine ⟨N, hNmin, ?_⟩
    have hmono :
        P.real (badTailEvent Bad N) ≤ P.real (Bad N) :=
      measureReal_mono (μ := P)
        (badTailEvent_badScaleEvent_subset
          (H := Hshift) (t := t) (α := α) hα_nonneg)
    exact hmono.trans hN
  have htail_tail :
      ∀ N : ℕ, Nmin ≤ N →
        P.real (badTailEvent Bad N) ≤
          Real.exp
            (-(((Real.rpow (3 : ℝ) ((N - Nmin : ℕ) : ℝ)) / B) ^ η)) := by
    intro N hNmin
    have hmono :
        P.real (badTailEvent Bad N) ≤ P.real (Bad N) :=
      measureReal_mono (μ := P)
        (badTailEvent_badScaleEvent_subset
          (H := Hshift) (t := t) (α := α) hα_nonneg)
    exact hmono.trans (by simpa [Hshift, Bad] using htail N hNmin)
  simpa [Hshift, Bad, X] using
    quenchedLocalizedEstimate_shifted_from_badTailBounds
      hP hStruct hΓ (t := t) (α := α) (η := η) (B := B)
      (Nentry := Nentry) (Nmin := Nmin)
      hη_pos hB hsmall_tail htail_tail

theorem exists_exp_neg_rpow_three_div_le
    {B η ε : ℝ} (hB : 0 < B) (hη : 0 < η) (hε : 0 < ε) :
    ∃ j : ℕ,
      Real.exp (-(((Real.rpow (3 : ℝ) (j : ℝ)) / B) ^ η)) ≤ ε := by
  have hpow :
      Tendsto (fun j : ℕ => Real.rpow (3 : ℝ) (j : ℝ)) atTop atTop := by
    simpa [Real.rpow_natCast] using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3) :
        Tendsto (fun j : ℕ => (3 : ℝ) ^ j) atTop atTop)
  have hdiv :
      Tendsto (fun j : ℕ => Real.rpow (3 : ℝ) (j : ℝ) / B) atTop atTop :=
    hpow.atTop_div_const hB
  have hrpow :
      Tendsto
        (fun j : ℕ => (Real.rpow (3 : ℝ) (j : ℝ) / B) ^ η)
        atTop atTop :=
    (tendsto_rpow_atTop hη).comp hdiv
  have hneg :
      Tendsto
        (fun j : ℕ => -((Real.rpow (3 : ℝ) (j : ℝ) / B) ^ η))
        atTop atBot :=
    tendsto_neg_atTop_atBot.comp hrpow
  have hexp :
      Tendsto
        (fun j : ℕ =>
          Real.exp (-(((Real.rpow (3 : ℝ) (j : ℝ)) / B) ^ η)))
        atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hevent :
      ∀ᶠ j : ℕ in atTop,
        Real.exp (-(((Real.rpow (3 : ℝ) (j : ℝ)) / B) ^ η)) ≤ ε :=
    hexp.eventually (Iic_mem_nhds hε)
  exact hevent.exists

/-- Tail-bound-only version of
`quenchedLocalizedEstimate_shifted_from_badTailBounds`.  The epsilon-smallness
input needed to remove the exceptional no-good-tail set follows from the same
stretched-exponential tail bound. -/
theorem quenchedLocalizedEstimate_shifted_from_badTailBound
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {t α η B : ℝ} {Nentry Nmin : ℕ}
    (hη_pos : 0 < η) (hB : 1 ≤ B)
    (htail :
      let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
        fun M N aω =>
          quenchedProbeEnvelope hP hStruct (Nentry + M) (Nentry + N) aω
      let Bad : ℕ → Set (RegCoeffField d) := badScaleEvent Hshift t α
      ∀ N : ℕ, Nmin ≤ N →
        P.real (badTailEvent Bad N) ≤
          Real.exp
            (-(((Real.rpow (3 : ℝ) ((N - Nmin : ℕ) : ℝ)) / B) ^ η))) :
    let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
      fun M N aω =>
        quenchedProbeEnvelope hP hStruct (Nentry + M) (Nentry + N) aω
    let Bad : ℕ → Set (RegCoeffField d) := badScaleEvent Hshift t α
    let X : RegCoeffField d → ℝ := quenchedMinimalScale Nmin Bad
    IsBigO P (gammaSigma η) X
      (3 * ((3 : ℝ) ^ Nmin) * B) ∧
      (∀ aω, 1 ≤ X aω) ∧
        ∀ (e : FullBlockVec d), dotProduct e e ≤ 1 →
          ∀ᵐ aω ∂P,
            ∀ {m n : ℕ},
              X aω ≤ (3 : ℝ) ^ m →
              n < m →
              (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) *
                  localizedLimitNormalizedJMax hP hStruct
                    (Nentry + m) (Nentry + n) e aω ≤
                ((3 : ℝ) ^ m / X aω) ^ (-α) := by
  intro Hshift Bad X
  have hB_pos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hsmall :
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, Nmin ≤ N ∧ P.real (badTailEvent Bad N) ≤ ε := by
    intro ε hε
    obtain ⟨j, hj⟩ :=
      exists_exp_neg_rpow_three_div_le
        (B := B) (η := η) (ε := ε) hB_pos hη_pos hε
    refine ⟨Nmin + j, Nat.le_add_right Nmin j, ?_⟩
    have htail_j :
        P.real (badTailEvent Bad (Nmin + j)) ≤
          Real.exp
            (-(((Real.rpow (3 : ℝ) (((Nmin + j) - Nmin : ℕ) : ℝ)) / B) ^ η)) := by
      simpa [Hshift, Bad] using
        htail (Nmin + j) (Nat.le_add_right Nmin j)
    exact htail_j.trans (by simpa [Nat.add_sub_cancel_left] using hj)
  simpa [Hshift, Bad, X] using
    quenchedLocalizedEstimate_shifted_from_badTailBounds
      hP hStruct hΓ (t := t) (α := α) (η := η) (B := B)
      (Nentry := Nentry) (Nmin := Nmin)
      hη_pos hB (by simpa [Hshift, Bad] using hsmall)
      (by simpa [Hshift, Bad] using htail)

end

end Section57
end Ch05
end Book
end Homogenization
