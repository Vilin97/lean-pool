/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadPairNoLog
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleSplit

/-! # Bad Scale Pair Two Branch -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped ENNReal

/-!
# Fixed-pair two-branch bad-scale estimates

This file starts the note-facing bad-scale proof at the fixed-pair level.  A
bad pair is split into the localized branch, where the selected intermediate
scale lies below `n`, and the crude branch, where it does not.  The concrete
estimate at the end uses the actual Section 5.7 localized and crude tail inputs;
it does not assume the desired bad-scale tail.
-/

noncomputable section

variable {Ω : Type*}

/-- Fixed-pair localized branch: the selected intermediate scale is below `n`. -/
def highPairBranchEvent
    (H : ℕ → ℕ → Ω → ℝ) (K a t α : ℝ) (q m n : ℕ) : Set Ω :=
  {ω | selectedBadPairScale K a t α q m n < n ∧
    ω ∈ badPairEvent H t α q m n}

/-- Fixed-pair crude branch: the selected intermediate scale is not below `n`. -/
def crudePairBranchEvent
    (H : ℕ → ℕ → Ω → ℝ) (K a t α : ℝ) (q m n : ℕ) : Set Ω :=
  {ω | n ≤ selectedBadPairScale K a t α q m n ∧
    ω ∈ badPairEvent H t α q m n}

theorem badPairEvent_subset_pair_branch_union
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q m n : ℕ} :
    badPairEvent H t α q m n ⊆
      highPairBranchEvent H K a t α q m n ∪
        crudePairBranchEvent H K a t α q m n := by
  intro ω hω
  by_cases hhigh : selectedBadPairScale K a t α q m n < n
  · exact Or.inl ⟨hhigh, hω⟩
  · exact Or.inr ⟨le_of_not_gt hhigh, hω⟩

variable [MeasurableSpace Ω]

/-- A softened fixed-pair tail.  If the tail parameter is below one this is
just a probability-one bound; if it is at least one it is the usual exponential
tail, with a harmless factor `exp 1` folded in. -/
def softPairTail (pref lam η : ℝ) : ℝ :=
  max 1 pref * Real.exp (1 - (max 1 lam) ^ η)

theorem softPairTail_nonneg {pref lam η : ℝ} :
    0 ≤ softPairTail pref lam η := by
  dsimp [softPairTail]
  exact mul_nonneg
    ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 pref))
    (Real.exp_pos _).le

theorem one_le_softPairTail_of_not_one_le_lam
    {pref lam η : ℝ} (hlam : ¬ 1 ≤ lam) :
    1 ≤ softPairTail pref lam η := by
  have hlam_le : lam ≤ 1 := le_of_not_ge hlam
  have hmax_lam : max 1 lam = 1 := max_eq_left hlam_le
  have hpref : 1 ≤ max 1 pref := le_max_left 1 pref
  simp [softPairTail, hmax_lam, hpref]

theorem pref_mul_exp_le_softPairTail_of_one_le_lam
    {pref lam η : ℝ} (_hpref : 0 ≤ pref) (hlam : 1 ≤ lam) :
    pref * Real.exp (-(lam ^ η)) ≤ softPairTail pref lam η := by
  have hmax_lam : max 1 lam = lam := max_eq_right hlam
  have hpref_le : pref ≤ max 1 pref := le_max_right 1 pref
  have hmax_pref_nonneg : 0 ≤ max 1 pref :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 pref)
  have hexp :
      Real.exp (-(lam ^ η)) ≤ Real.exp (1 - lam ^ η) :=
    Real.exp_le_exp.mpr (by linarith)
  simpa [softPairTail, hmax_lam] using
    mul_le_mul hpref_le hexp (Real.exp_pos _).le hmax_pref_nonneg

theorem softPairTail_mono_lam
    {pref lam₁ lam₂ η : ℝ} (hη : 0 < η) (hlam : lam₁ ≤ lam₂) :
    softPairTail pref lam₂ η ≤ softPairTail pref lam₁ η := by
  have hmax : max 1 lam₁ ≤ max 1 lam₂ :=
    max_le (le_max_left 1 lam₂) (hlam.trans (le_max_right 1 lam₂))
  have hbase : 0 ≤ max 1 lam₁ :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 lam₁)
  have hpow : (max 1 lam₁) ^ η ≤ (max 1 lam₂) ^ η :=
    Real.rpow_le_rpow hbase hmax hη.le
  have hexp :
      Real.exp (1 - (max 1 lam₂) ^ η) ≤
        Real.exp (1 - (max 1 lam₁) ^ η) :=
    Real.exp_le_exp.mpr (by linarith)
  exact mul_le_mul_of_nonneg_left hexp
    ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 pref))

/-- Taking the better of two soft fixed-pair tails replaces the two exponents
by their maximum. -/
theorem min_softPairTail_le_maxExponent
    {pref lam₁ lam₂ η₁ η₂ : ℝ} :
    min (softPairTail pref lam₁ η₁) (softPairTail pref lam₂ η₂) ≤
      max 1 pref *
        Real.exp
          (1 - max ((max 1 lam₁) ^ η₁) ((max 1 lam₂) ^ η₂)) := by
  by_cases hcmp : (max 1 lam₁) ^ η₁ ≤ (max 1 lam₂) ^ η₂
  · have hmax :
        max ((max 1 lam₁) ^ η₁) ((max 1 lam₂) ^ η₂) =
          (max 1 lam₂) ^ η₂ := max_eq_right hcmp
    calc
      min (softPairTail pref lam₁ η₁) (softPairTail pref lam₂ η₂)
          ≤ softPairTail pref lam₂ η₂ := min_le_right _ _
      _ = max 1 pref *
          Real.exp
            (1 - max ((max 1 lam₁) ^ η₁) ((max 1 lam₂) ^ η₂)) := by
            simp [softPairTail, hmax]
  · have hmax :
        max ((max 1 lam₁) ^ η₁) ((max 1 lam₂) ^ η₂) =
          (max 1 lam₁) ^ η₁ := max_eq_left (le_of_not_ge hcmp)
    calc
      min (softPairTail pref lam₁ η₁) (softPairTail pref lam₂ η₂)
          ≤ softPairTail pref lam₁ η₁ := min_le_left _ _
      _ = max 1 pref *
          Real.exp
            (1 - max ((max 1 lam₁) ^ η₁) ((max 1 lam₂) ^ η₂)) := by
            simp [softPairTail, hmax]

theorem le_maxExponent_softPairTail_of_le_both
    {x pref lam₁ lam₂ η₁ η₂ : ℝ}
    (h₁ : x ≤ softPairTail pref lam₁ η₁)
    (h₂ : x ≤ softPairTail pref lam₂ η₂) :
    x ≤
      max 1 pref *
        Real.exp
          (1 - max ((max 1 lam₁) ^ η₁) ((max 1 lam₂) ^ η₂)) := by
  exact (le_min h₁ h₂).trans min_softPairTail_le_maxExponent

theorem measureReal_highPairBranchEvent_le_softTail
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q m n : ℕ}
    {pref lam η : ℝ}
    (hpref : 0 ≤ pref)
    (htail :
      selectedBadPairScale K a t α q m n < n →
        1 ≤ lam →
          μ.real (badPairEvent H t α q m n) ≤
            pref * Real.exp (-(lam ^ η))) :
    μ.real (highPairBranchEvent H K a t α q m n) ≤
      softPairTail pref lam η := by
  by_cases hhigh : selectedBadPairScale K a t α q m n < n
  · by_cases hlam : 1 ≤ lam
    · have hmono :
          μ.real (highPairBranchEvent H K a t α q m n) ≤
            μ.real (badPairEvent H t α q m n) :=
        measureReal_mono (μ := μ) (by
          intro ω hω
          exact hω.2)
      exact
        hmono.trans
          ((htail hhigh hlam).trans
            (pref_mul_exp_le_softPairTail_of_one_le_lam hpref hlam))
    · exact
        (measureReal_le_one
          (μ := μ) (s := highPairBranchEvent H K a t α q m n)).trans
          (one_le_softPairTail_of_not_one_le_lam hlam)
  · have hempty : highPairBranchEvent H K a t α q m n = ∅ := by
      ext ω
      simp [highPairBranchEvent, hhigh]
    rw [hempty]
    simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
    dsimp [softPairTail]
    exact mul_nonneg
      ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 pref))
      (Real.exp_pos _).le

theorem measureReal_crudePairBranchEvent_le_softTail
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q m n : ℕ}
    {pref lam η : ℝ}
    (hpref : 0 ≤ pref)
    (htail :
      n ≤ selectedBadPairScale K a t α q m n →
        1 ≤ lam →
          μ.real (badPairEvent H t α q m n) ≤
            pref * Real.exp (-(lam ^ η))) :
    μ.real (crudePairBranchEvent H K a t α q m n) ≤
      softPairTail pref lam η := by
  by_cases hcrude : n ≤ selectedBadPairScale K a t α q m n
  · by_cases hlam : 1 ≤ lam
    · have hmono :
          μ.real (crudePairBranchEvent H K a t α q m n) ≤
            μ.real (badPairEvent H t α q m n) :=
        measureReal_mono (μ := μ) (by
          intro ω hω
          exact hω.2)
      exact
        hmono.trans
          ((htail hcrude hlam).trans
            (pref_mul_exp_le_softPairTail_of_one_le_lam hpref hlam))
    · exact
        (measureReal_le_one
          (μ := μ) (s := crudePairBranchEvent H K a t α q m n)).trans
          (one_le_softPairTail_of_not_one_le_lam hlam)
  · have hempty : crudePairBranchEvent H K a t α q m n = ∅ := by
      ext ω
      simp [crudePairBranchEvent, hcrude]
    rw [hempty]
    simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
    dsimp [softPairTail]
    exact mul_nonneg
      ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 pref))
      (Real.exp_pos _).le

theorem measureReal_badPairEvent_le_soft_two_branch
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q m n : ℕ}
    {prefHigh lamHigh ηHigh prefCrude lamCrude ηCrude : ℝ}
    (hprefHigh : 0 ≤ prefHigh) (hprefCrude : 0 ≤ prefCrude)
    (hhigh :
      selectedBadPairScale K a t α q m n < n →
        1 ≤ lamHigh →
          μ.real (badPairEvent H t α q m n) ≤
            prefHigh * Real.exp (-(lamHigh ^ ηHigh)))
    (hcrude :
      n ≤ selectedBadPairScale K a t α q m n →
        1 ≤ lamCrude →
          μ.real (badPairEvent H t α q m n) ≤
            prefCrude * Real.exp (-(lamCrude ^ ηCrude))) :
    μ.real (badPairEvent H t α q m n) ≤
      softPairTail prefHigh lamHigh ηHigh +
        softPairTail prefCrude lamCrude ηCrude := by
  calc
    μ.real (badPairEvent H t α q m n)
        ≤ μ.real
            (highPairBranchEvent H K a t α q m n ∪
              crudePairBranchEvent H K a t α q m n) :=
          measureReal_mono (μ := μ)
            (badPairEvent_subset_pair_branch_union
              (H := H) (K := K) (a := a) (t := t) (α := α)
              (q := q) (m := m) (n := n))
    _ ≤ μ.real (highPairBranchEvent H K a t α q m n) +
          μ.real (crudePairBranchEvent H K a t α q m n) :=
          measureReal_union_le _ _
    _ ≤ softPairTail prefHigh lamHigh ηHigh +
          softPairTail prefCrude lamCrude ηCrude := by
          exact add_le_add
            (measureReal_highPairBranchEvent_le_softTail
              (μ := μ) (H := H) (K := K) (a := a) (t := t)
              (α := α) (q := q) (m := m) (n := n)
              hprefHigh hhigh)
            (measureReal_crudePairBranchEvent_le_softTail
              (μ := μ) (H := H) (K := K) (a := a) (t := t)
              (α := α) (q := q) (m := m) (n := n)
              hprefCrude hcrude)

/-- Concrete fixed-pair two-branch estimate for the shifted finite-probe
envelope.  The two branches are still expressed with their raw tail parameters;
the next deterministic step lowers these parameters to the manuscript
`3^(b*q)` and `3^(t*q)` scales before summing. -/
theorem measureReal_shiftedBadPairEvent_quenchedProbeEnvelope_le_soft_two_branch
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Ccrude Centry a : ℝ,
      0 < Cfluct ∧ 0 < Ccrude ∧ 0 < Centry ∧ 0 < a ∧
      ∀ {t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {q m n : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let x : ℝ :=
          αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
        let ell : ℕ := selectedBadPairScale K a t αbad q m n
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let D : Finset (TriadicCube d) :=
          descendantsAtScale
            (originCube d (((N0 + m : ℕ) : ℤ)))
            (((N0 + n : ℕ) : ℤ))
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let tau : ℝ := min σ 2
        let highScale : ℝ :=
          Cfluct *
            (3 : ℝ) ^
              ((-(d : ℝ) / 2) * ((n - ell : ℕ) : ℝ)) *
            hΓ.thetaHat ^ (2 : ℕ)
        let T : ℝ := Real.rpow (3 : ℝ) (-x)
        let highLam : ℝ := T / (2 * K * highScale)
        let crudeScale : ℝ := K * (Ccrude * hΓ.thetaHat ^ (2 : ℕ))
        let crudeLam : ℝ := T / crudeScale
        let pref : ℝ := (S.card : ℝ) * (D.card : ℝ)
        n < m → q ≤ m →
        P.real (badPairEvent Hshift t αbad q m n) ≤
          softPairTail pref highLam tau +
            softPairTail pref crudeLam σ := by
  obtain ⟨Cfluct, Centry, a, hCfluct, hCentry, ha, hhighRaw⟩ :=
    measureReal_shiftedHigh_badPairEvent_quenchedProbeEnvelope_le_card_mul_card_mul_exp_noLog
      (d := d) (σ := σ) hσ_pos params
  obtain ⟨Ccrude, hCcrude, hcrudeRaw⟩ :=
    measureReal_shiftedCrude_badPairEvent_quenchedProbeEnvelope_le_card_mul_card_mul_exp_noLog
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Cfluct, Ccrude, Centry, a, hCfluct, hCcrude, hCentry, ha, ?_⟩
  intro t αbad P hP hStruct hΓ hσ_eq hparams q m n
  dsimp only
  intro hnm hqm
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let K : ℝ := quenchedProbeEnvelopeConst d
  let x : ℝ :=
    αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
  let ell : ℕ := selectedBadPairScale K a t αbad q m n
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω =>
      quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
  let D : Finset (TriadicCube d) :=
    descendantsAtScale
      (originCube d (((N0 + m : ℕ) : ℤ)))
      (((N0 + n : ℕ) : ℤ))
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let tau : ℝ := min σ 2
  let highScale : ℝ :=
    Cfluct *
      (3 : ℝ) ^ ((-(d : ℝ) / 2) * ((n - ell : ℕ) : ℝ)) *
      hΓ.thetaHat ^ (2 : ℕ)
  let T : ℝ := Real.rpow (3 : ℝ) (-x)
  let highLam : ℝ := T / (2 * K * highScale)
  let crudeScale : ℝ := K * (Ccrude * hΓ.thetaHat ^ (2 : ℕ))
  let crudeLam : ℝ := T / crudeScale
  let pref : ℝ := (S.card : ℝ) * (D.card : ℝ)
  have hpref : 0 ≤ pref := by
    dsimp [pref]
    positivity
  refine
    measureReal_badPairEvent_le_soft_two_branch
      (μ := P) (H := Hshift) (K := K) (a := a) (t := t)
      (α := αbad) (q := q) (m := m) (n := n)
      (prefHigh := pref) (lamHigh := highLam) (ηHigh := tau)
      (prefCrude := pref) (lamCrude := crudeLam) (ηCrude := σ)
      hpref hpref ?_ ?_
  · intro hell hlam
    have hraw :=
      hhighRaw (t := t) (αbad := αbad) hP hStruct hΓ hσ_eq hparams
        (q := q) (m := m) (n := n)
    dsimp only at hraw
    have htail :
        P.real (badPairEvent Hshift t αbad q m n) ≤
          (S.card : ℝ) * ((D.card : ℝ) * Real.exp (-(highLam ^ tau))) := by
      simpa [K, x, ell, selectedBadPairScale, N0, Hshift, D, S, tau,
        highScale, T, highLam] using
        hraw hell hnm hqm hlam
    simpa [pref, mul_assoc] using htail
  · intro _hcrude hlam
    have hraw :=
      hcrudeRaw (t := t) (αbad := αbad) hP hStruct hΓ hσ_eq hparams
        (N0 := N0) (q := q) (m := m) (n := n)
    dsimp only at hraw
    have htail :
        P.real (badPairEvent Hshift t αbad q m n) ≤
          (S.card : ℝ) * ((D.card : ℝ) * Real.exp (-(crudeLam ^ σ))) := by
      simpa [K, Hshift, x, D, S, crudeScale, T, crudeLam] using
        hraw hnm hqm hlam
    simpa [pref, mul_assoc] using htail

end

end Section57
end Ch05
end Book
end Homogenization
